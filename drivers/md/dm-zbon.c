//// SPDX-License-Identifier: GPL-2.0-only

#include "dm.h"
#include <linux/module.h>
#include <linux/init.h>
#include <linux/blkdev.h>
#include <linux/bio.h>
#include <linux/slab.h>
#include <linux/atomic.h>
#include <linux/delay.h>
#include <linux/device-mapper.h>
#include <linux/dm-kcopyd.h>

#define DM_MSG_PREFIX		"zbon"
#define ZB_MIN_BIOS		8192
#define ZB_MAX_ACTIVE_WORKERS	32
#define ZB_MAX_ACTIVE_META	((PAGE_SIZE - 8) / 24)

struct zbon_zone {
	struct blk_zone		blkz;
	struct zbon_buffer	*buffer;
	sector_t		flush_offset; // TODO: move to buffer
	spinlock_t		lock;
	struct list_head	work_list;
	struct mutex		work_mtx;
};

struct zbon_buffer {
	refcount_t		ref;
	sector_t		start;
	int			index;
	bool			put_after_sync;
	struct zbon_zone	*zone;
};


#define ZB_MAGIC	((((unsigned int)('Z')) << 24) | \
			 (((unsigned int)('B')) << 16) | \
			 (((unsigned int)('O')) <<  8) | \
			  ((unsigned int)('N')))

struct zbon_buffer_metadata {
	__le32				zone_index;
	__le32				buffer_index;
	__le32				wp_offset;
};

struct zbon_metadata {
	__le32				magic;
	__le32				nr_active_buffers;
	struct zbon_buffer_metadata	buffer_metadata[];
};

struct zbon_c {
	struct dm_dev		*dev;
	struct dm_dev		*cache_dev;
	struct block_device	*bdev;
	struct block_device	*cache_bdev;
	unsigned long		nr_zones;
	unsigned long		zone_nr_sectors;
	unsigned long		max_active_zones;

	struct xarray zones;
	struct zbon_buffer	*buffers;
	unsigned long		*buffer_bits;

	struct bio_set		bio_set;

	struct workqueue_struct *sync_wq;
	struct workqueue_struct *flush_wq;
	struct dm_kcopyd_client	*kc;

	sector_t		min_write_sectors;

	atomic_t		sectors_to_flush;
	sector_t		throttle_limit;

	struct page		*metadata_page;
	void			*metadata;
	struct mutex		metadata_mtx;

	spinlock_t		sync_lock;
	struct bio_list		presync_bios;
	struct bio_list		postsync_bios;

};

enum {
	DEFERRED_FLUSH,
	DEFERRED_FULL,
	DEFERRED_ZONE_OP
};

struct zbon_zone_workitem {
	int			type;
	struct bio		*bio;
	struct zbon_zone	*zone;
	struct list_head	list;
};

struct zbon_deferred_work {
	struct work_struct		work;
	struct zbon_c			*zc;
	struct zbon_zone		*zone;
};

struct zbon_sync_work {
	struct work_struct		work;
	struct zbon_c			*zc;
};

struct zbon_postsync_work {
	struct work_struct		work;
	struct zbon_c			*zc;
	struct zbon_zone		*zone;
	bool				*free_buffer;
	struct bio			*bio;
};

struct zbon_bioctx {
	struct bio *bio;
	struct zbon_c *zc;
	unsigned long *done;
	struct zbon_buffer *buffer;
};

enum {
	ZBON_FLUSH_KCOPY,
	ZBON_FLUSH_BIO_END,
};

struct zbon_flush {
	int kc_err;
	unsigned long flags;
};

static inline bool zbon_zone_is_active(struct blk_zone *blkz) {
	return ((blkz->cond == BLK_ZONE_COND_IMP_OPEN) ||
	        (blkz->cond == BLK_ZONE_COND_EXP_OPEN) ||
	        (blkz->cond == BLK_ZONE_COND_CLOSED));

}

static void zbon_buffer_get(struct zbon_buffer *buffer) {
	refcount_inc(&buffer->ref);
}

static void zbon_buffer_put(struct zbon_buffer *buffer, struct zbon_c *zc) {
	if (refcount_dec_and_test(&buffer->ref)) {
		clear_bit(buffer->index, zc->buffer_bits);
	}
}

static int zbon_buffer_allocate(struct zbon_zone *zone, struct zbon_c *zc) {
	int i;


	for (i = 0; i < zc->max_active_zones; i++) {
		if (test_and_set_bit(i, zc->buffer_bits) == 0) {
			refcount_set(&zc->buffers[i].ref, 1);
			zone->buffer = &zc->buffers[i];
			zone->flush_offset = zone->blkz.wp - zone->blkz.start;
			zone->buffer->zone = zone;
			return 0;
		}
	}

	return -EBUSY;
}

static void zbon_buffer_free(struct zbon_zone *zone) {
	zone->buffer->put_after_sync = true;
	zone->buffer = NULL;
}


int zbon_init_zone(struct blk_zone *blkz, unsigned int zone_id, void *data)
{
	struct zbon_c *zc = data;
	struct zbon_zone *zone = kzalloc(sizeof(struct zbon_zone), GFP_KERNEL);

	if (!zone)
		return -ENOMEM;

	if (xa_insert(&zc->zones, zone_id, zone, GFP_KERNEL)) {
		kfree(zone);
		return -EBUSY;
	}

	memcpy(&zone->blkz, blkz, sizeof(struct blk_zone));
	zone->buffer = NULL;
	INIT_LIST_HEAD(&zone->work_list);
	spin_lock_init(&zone->lock);
	mutex_init(&zone->work_mtx);

	return 0;
}

static int zbon_init_zones(struct zbon_c *zc)
{
	int ret;
	ret  = blkdev_report_zones(zc->bdev, 0, BLK_ALL_ZONES,
				   zbon_init_zone, zc);
	if (ret < 0) {
		DMDEBUG("Failed to report zones, error %d", ret);
		return ret;
	}

	return 0;
}

static int zbon_rdwr_block(struct block_device *bdev, enum req_op op,
			  sector_t sector, struct page *page)
{
	struct bio *bio;
	int ret;

	bio = bio_alloc(bdev, 1, op | REQ_SYNC | REQ_META | REQ_PRIO,
			GFP_NOIO);
	bio->bi_iter.bi_sector = sector;
	ret = bio_add_page(bio, page, PAGE_SIZE, 0);
	if (ret == PAGE_SIZE)
		ret = submit_bio_wait(bio);

	bio_put(bio);

	return ret;
}

static int zbon_read_state(struct zbon_c *zc) {
	struct zbon_metadata *metadata = zc->metadata;
	int ret;
	int i,n;

	ret = zbon_rdwr_block(zc->cache_bdev, REQ_OP_READ, 0, zc->metadata_page);
	if (ret)
		return ret;

	if (le32_to_cpu(metadata->magic) != ZB_MAGIC) {
		return -EINVAL;
	}

	n = le32_to_cpu(metadata->nr_active_buffers);

	for (i = 0; i < n ; i++) {
		struct zbon_buffer_metadata *m = &metadata->buffer_metadata[i];
		struct zbon_zone *z;
		unsigned int bi;

		z = xa_load(&zc->zones, le32_to_cpu(m->zone_index));
		bi = le32_to_cpu(m->buffer_index);

		if (test_and_set_bit(bi, zc->buffer_bits) == 0) {
			sector_t new_wp  = z->blkz.start + le32_to_cpu(m->wp_offset);
			z->flush_offset = z->blkz.wp - z->blkz.start;
			if (new_wp > z->blkz.wp) {
				if (z->blkz.cond == BLK_ZONE_COND_EMPTY)
					z->blkz.cond = BLK_ZONE_COND_IMP_OPEN;
				z->blkz.wp = new_wp;
			}
			z->buffer = &zc->buffers[bi];
			zc->buffers[bi].zone = z;
			refcount_set(&zc->buffers[bi].ref, 1);
		} else {
			DMERR("Metadata corruption - two zones mapped to one buffer \n");
		}
	}

	return ret;
}

static int zbon_store_state(struct zbon_c *zc) {
	struct zbon_metadata *metadata = zc->metadata;
	unsigned long flags;
	int n = 0;
	unsigned int i, ret;

	mutex_lock(&zc->metadata_mtx);
	metadata->magic = cpu_to_le32(ZB_MAGIC);

	for (i = 0; i < zc->max_active_zones; i++) {
		struct zbon_buffer *buffer = &zc->buffers[i];

		if (test_bit(i, zc->buffer_bits)) {
			struct zbon_buffer_metadata *m = &metadata->buffer_metadata[n];

			if (buffer->put_after_sync) {
				buffer->put_after_sync = false;
				buffer->zone = NULL;
				zbon_buffer_put(buffer, zc);
			} else {
				struct zbon_zone *z = buffer->zone;
				spin_lock_irqsave(&z->lock, flags);
				if (z->buffer) {
					m->zone_index = cpu_to_le32(z->blkz.start / zc->zone_nr_sectors);
					m->buffer_index = cpu_to_le32(z->buffer->index);
					m->wp_offset = cpu_to_le32(z->blkz.wp - z->blkz.start);
					n++;
				}
				spin_unlock_irqrestore(&z->lock, flags);
			}

		}
	}

	metadata->nr_active_buffers = n;
	ret = zbon_rdwr_block(zc->cache_bdev, REQ_OP_WRITE, 0, zc->metadata_page);

	mutex_unlock(&zc->metadata_mtx);

	return ret;
}

static void zbon_sync_work(struct work_struct *w) {
	struct zbon_sync_work *work = container_of(w, struct zbon_sync_work, work);
	struct zbon_c *zc = work->zc;
	unsigned long flags;
	struct bio *bio;
	int sync_status;

	sync_status = zbon_store_state(work->zc);


	while (1) {
		spin_lock_irqsave(&zc->sync_lock, flags);
		bio = bio_list_pop(&zc->presync_bios);
		spin_unlock_irqrestore(&zc->sync_lock, flags);

		if (!bio)
			break;

		if (sync_status) {
			bio->bi_status = BLK_STS_IOERR;
			bio_endio(bio);
		} else {
			submit_bio_noacct(bio);
		}
	}

	while (1) {
		spin_lock_irqsave(&zc->sync_lock, flags);
		bio = bio_list_pop(&zc->postsync_bios);
		spin_unlock_irqrestore(&zc->sync_lock, flags);

		if (!bio)
			break;

		if (sync_status)
			bio->bi_status = BLK_STS_IOERR;

		bio_endio(bio);
	}

	kfree(work);
}

static int zbon_queue_sync_work(struct bio *bio, struct bio_list *sync_biolist,
			        struct zbon_c *zc) {
	struct zbon_sync_work *sw;
	unsigned long flags;

	sw = kzalloc(sizeof(struct zbon_sync_work), GFP_NOIO);
	if (!sw) {
		return DM_MAPIO_KILL;
	}

	INIT_WORK(&sw->work, zbon_sync_work);

	sw->zc = zc;

	spin_lock_irqsave(&zc->sync_lock, flags);
	bio_list_add(sync_biolist, bio);
	spin_unlock_irqrestore(&zc->sync_lock,flags);

	queue_work(zc->sync_wq, &sw->work);

	return DM_MAPIO_SUBMITTED;
}


static int zbon_update_zone_state(struct bio *bio, struct zbon_zone *z, struct zbon_c *zc)
{
	switch (bio_op(bio)) {
	case REQ_OP_WRITE:
		/* Zone full ? */
		if (z->blkz.wp ==  z->blkz.start + z->blkz.capacity) {
			z->blkz.wp = z->blkz.start + z->blkz.len;
			z->blkz.cond = BLK_ZONE_COND_FULL;
		}
		return 0;
	case REQ_OP_ZONE_OPEN:
		if (z->blkz.cond == BLK_ZONE_COND_EXP_OPEN) {
			return 0;
		}
		if (z->blkz.cond == BLK_ZONE_COND_IMP_OPEN ||
		    z->blkz.cond == BLK_ZONE_COND_CLOSED) {
			z->blkz.cond = BLK_ZONE_COND_EXP_OPEN;
			return 0;
		}
		if (z->blkz.cond == BLK_ZONE_COND_EMPTY) {
			z->blkz.cond = BLK_ZONE_COND_EXP_OPEN;
			return 0;
		}
		return -EINVAL;
	case REQ_OP_ZONE_CLOSE:
		if (z->blkz.cond == BLK_ZONE_COND_EXP_OPEN ||
		    z->blkz.cond == BLK_ZONE_COND_IMP_OPEN) {
			z->blkz.cond = BLK_ZONE_COND_CLOSED;
			return 0;
		}
		return -EINVAL;
	case REQ_OP_ZONE_FINISH:
		if (z->blkz.cond == BLK_ZONE_COND_FULL ||
		    z->blkz.cond == BLK_ZONE_COND_EMPTY ||
		    zbon_zone_is_active(&z->blkz)) {
			z->blkz.cond = BLK_ZONE_COND_FULL;
			z->blkz.wp = z->blkz.start + z->blkz.len;
			z->flush_offset = z->blkz.len;
			return 0;
		}
		return -EINVAL;
	case REQ_OP_ZONE_RESET:
		if (z->blkz.cond == BLK_ZONE_COND_FULL ||
		    z->blkz.cond == BLK_ZONE_COND_EMPTY ||
		    zbon_zone_is_active(&z->blkz)) {
			z->blkz.cond = BLK_ZONE_COND_EMPTY;
			z->blkz.wp = z->blkz.start;
			z->flush_offset = 0;
			if (z->buffer != NULL) {
				zbon_buffer_free(z);
			}
			return 0;
		}
		return -EINVAL;
	default:
		DMERR("Unsupported BIO operation 0x%x", bio_op(bio));
	}

	return -EINVAL;
}

static void zbon_flush_kcopy_end(int read_err, unsigned long write_err, void *context)
{
	struct zbon_flush *zfc = context;
	if (read_err || write_err)
		zfc->kc_err = -EIO;
	else
		zfc->kc_err = 0;

	clear_bit_unlock(ZBON_FLUSH_KCOPY, &zfc->flags);
	smp_mb__after_atomic();
	wake_up_bit(&zfc->flags, ZBON_FLUSH_KCOPY);
}

static void zbon_submit_flush_clone_wait(struct bio *bio)
{
	struct zbon_bioctx *bioctx = bio->bi_private;
	unsigned long done;

	bioctx->done = &done;
	set_bit(1, &done);
	submit_bio_noacct(bio);
	wait_on_bit_io(&done, 1, TASK_UNINTERRUPTIBLE);
}

static int zbon_flush(struct zbon_zone *z, bool align, struct zbon_c *zc) {
	struct dm_io_region src, dst;
	struct zbon_flush zfc;
	sector_t wp, flush_offset;
	sector_t to_flush;
	sector_t pad;
	unsigned long flags;

	spin_lock_irqsave(&z->lock, flags);
	wp = z->blkz.wp;
	flush_offset = z->flush_offset;
	to_flush = wp - (z->blkz.start + flush_offset);
	if  (z->buffer ==  NULL || to_flush == 0) {
		spin_unlock_irqrestore(&z->lock, flags);
		return 0;
	}
	spin_unlock_irqrestore(&z->lock, flags);

	pad = zc->min_write_sectors - to_flush % zc->min_write_sectors;
	if (align && pad != zc->min_write_sectors) {
		dst.bdev = zc->cache_bdev;
		dst.sector = wp;
		dst.count = pad;

		set_bit(ZBON_FLUSH_KCOPY, &zfc.flags);
		dm_kcopyd_zero(zc->kc, 1, &dst, DM_KCOPYD_WRITE_SEQ,
		       zbon_flush_kcopy_end, &zfc);

		/* Wait for padding to complete */
		wait_on_bit_io(&zfc.flags, ZBON_FLUSH_KCOPY,
		       TASK_UNINTERRUPTIBLE);
		if (zfc.kc_err) {
			DMERR("There was an error during zero padding: %d", zfc.kc_err);
			return zfc.kc_err;
		}

		atomic_sub(to_flush, &zc->sectors_to_flush);
		to_flush += pad;

	} else {
		to_flush -= to_flush % zc->min_write_sectors;
		atomic_sub(to_flush, &zc->sectors_to_flush);
	}


	spin_lock_irqsave(&z->lock, flags);
	src.bdev = zc->cache_bdev;
	src.sector = z->buffer->start + flush_offset;
	src.count = to_flush;
	dst.bdev = zc->bdev;
	dst.sector = z->blkz.start + z->flush_offset;
	dst.count = src.count;
	spin_unlock_irqrestore(&z->lock, flags);

	set_bit(ZBON_FLUSH_KCOPY, &zfc.flags);
	dm_kcopyd_copy(zc->kc, &src, 1, &dst, DM_KCOPYD_WRITE_SEQ,
		       zbon_flush_kcopy_end, &zfc);

	/* Wait for copy to complete */
	wait_on_bit_io(&zfc.flags, ZBON_FLUSH_KCOPY,
		       TASK_UNINTERRUPTIBLE);

	if (zfc.kc_err) {
		DMERR("There was an error during kcopy: %d", zfc.kc_err);
		return zfc.kc_err;
	}

	spin_lock_irqsave(&z->lock, flags);
	z->flush_offset += to_flush;
	if (z->blkz.wp ==  z->blkz.start + z->blkz.capacity && z->flush_offset == z->blkz.capacity) {
		zbon_buffer_free(z);
	}
	spin_unlock_irqrestore(&z->lock, flags);

	return 0;
}

static void zbon_deferred_work(struct work_struct *w)
{
	struct zbon_deferred_work *work = container_of(w, struct zbon_deferred_work,
						       work);
	struct zbon_zone_workitem *wi;
	struct zbon_zone *z = work->zone;
	struct zbon_c *zc = work->zc;
	bool align = false;
	struct bio *bio;
	int type;
	int ret;
	unsigned long flags;

	mutex_lock(&z->work_mtx);

	/* Pop the next work item off the per-zone list */
	spin_lock_irqsave(&z->lock, flags);
	wi = list_first_entry(&z->work_list, struct zbon_zone_workitem, list);
	list_del(&wi->list);
	spin_unlock_irqrestore(&z->lock, flags);

	type = wi->type;
	bio = wi->bio;

	if (type == DEFERRED_ZONE_OP && bio_op(bio) == REQ_OP_ZONE_FINISH)
		align = true;

	ret = zbon_flush(z, align, zc);
	if (ret)
		DMERR("There was an error zone flush: %d", ret);

	if (type == DEFERRED_ZONE_OP) {
		if (bio->bi_opf & REQ_PREFLUSH)
			zbon_store_state(zc);
		zbon_submit_flush_clone_wait(bio);
	} else if (type == DEFERRED_FULL) {
		spin_lock_irqsave(&z->lock, flags);
		zbon_update_zone_state(bio, z, zc);
		spin_unlock_irqrestore(&z->lock, flags);
		bio_advance(bio, bio->bi_iter.bi_size);

		/* We need a sync to safely free the buffer */
		zbon_queue_sync_work(bio, &zc->postsync_bios, zc);
	}

	kfree(work);
	kfree(wi);

	mutex_unlock(&z->work_mtx);
}

static int zbon_ctr(struct dm_target *ti, unsigned int argc, char **argv)
{
	struct mapped_device *md;
	sector_t max_zone_caches;
	struct zbon_c *zc;
	unsigned long long throttle_limit;
	char dummy;
	int ret;
	int i;

	if (argc != 3) {
		ti->error = "Invalid argument count";
		return -EINVAL;
	}

	if (sscanf(argv[2], "%llu%c", &throttle_limit, &dummy) != 1 || throttle_limit == 0) {
		ti->error = "Invalid throttle limit";
		return -EINVAL;
	}

	zc = kzalloc(sizeof(struct zbon_c), GFP_KERNEL);
	if (zc == NULL) {
		ti->error = "Cannot allocate zbon context";
		return -ENOMEM;
	}

	ret = dm_get_device(ti, argv[1], dm_table_get_mode(ti->table), &zc->dev);
	if (ret) {
		ti->error = "Zoned device lookup failed";
		goto err_free_zc;
	}

	ret = dm_get_device(ti, argv[0], dm_table_get_mode(ti->table), &zc->cache_dev);
	if (ret) {
		dm_put_device(ti, zc->dev);
		ti->error = "Cache device lookup failed";
		goto err_free_zc;
	}

	zc->cache_bdev = zc->cache_dev->bdev;
	if (bdev_zoned_model(zc->cache_bdev) != BLK_ZONED_NONE) {
		ti->error = "Cache device must be a conventional block device";
		ret = -EINVAL;
		goto err_put_devices;
	}

	zc->bdev = zc->dev->bdev;
	if (bdev_zoned_model(zc->bdev) != BLK_ZONED_HM) {
		ti->error = "Device must be a host managed zoned block device";
		ret = -EINVAL;
		goto err_put_devices;
	}

	xa_init(&zc->zones);
	atomic_set(&zc->sectors_to_flush, 0);

	zc->nr_zones = bdev_nr_zones(zc->bdev);
	zc->zone_nr_sectors = bdev_zone_sectors(zc->bdev);
	zc->max_active_zones = bdev_max_active_zones(zc->bdev);


	zc->min_write_sectors = to_sector(bdev_io_min(zc->bdev));
	zc->throttle_limit = (throttle_limit * 1024 * 1024 * 1024) >> 9;
	max_zone_caches = bdev_nr_sectors(zc->cache_bdev) / zc->zone_nr_sectors;
	if (zc->max_active_zones == 0 || zc->max_active_zones > max_zone_caches) {
		zc->max_active_zones = max_zone_caches;
	}

	if (zc->max_active_zones > ZB_MAX_ACTIVE_META)
	       zc->max_active_zones = ZB_MAX_ACTIVE_META;

	if (zbon_init_zones(zc)) {
		ti->error = "Failed to initialize zones";
		ret = -ENOMEM;
		goto err_put_devices;
	}

	zc->buffers = kzalloc(sizeof(struct zbon_buffer) *
			      zc->max_active_zones , GFP_KERNEL);
	if (zc->buffers == NULL)
		goto err_free_zones;


	zc->buffer_bits = kzalloc(dm_div_up(zc->max_active_zones,
					    sizeof(unsigned long)), GFP_KERNEL);
	if (zc->buffer_bits == NULL) {
		kfree(zc->buffers);
		goto err_free_buffers;
	}

	for (i = 0; i < zc->max_active_zones; i++) {
		// TODO: if capacity != size we could save space..
		zc->buffers[i].start = i * zc->zone_nr_sectors + (PAGE_SIZE >> 9);
		zc->buffers[i].index = i;
		zc->buffers[i].zone = NULL;
		refcount_set(&zc->buffers[i].ref, 0);
	}


	if (bioset_init(&zc->bio_set, ZB_MIN_BIOS, 0, 0)) {
		ti->error = "Create BIO set failed";
		ret = -ENOMEM;
		goto err_free_buffer_bits;
	}

	md = dm_table_get_md(ti->table);
	dm_disk(md)->max_open_zones = zc->max_active_zones;
	dm_disk(md)->max_active_zones = zc->max_active_zones;

	zc->sync_wq = alloc_ordered_workqueue("zbon_swq_%s", 0, dm_disk(md)->disk_name);
	if (!zc->sync_wq) {
		ti->error = "Create sync queue failed";
		ret = -ENOMEM;
		goto err_bioset_exit;
	}
	spin_lock_init(&zc->sync_lock);

	zc->flush_wq = alloc_workqueue("zbon_fwq_%s", 0, ZB_MAX_ACTIVE_WORKERS,
				       dm_disk(md)->disk_name);
	if (!zc->flush_wq) {
		ti->error = "Create flush queue failed";
		ret = -ENOMEM;
		goto err_destroy_sync_workqueue;
	}

	zc->kc = dm_kcopyd_client_create(NULL);
	if (IS_ERR(zc->kc)) {
		ti->error = "Failed to create kcopyd client";
		ret = -ENOMEM;
		goto err_destroy_flush_workqueue;
	}

	zc->metadata_page = alloc_page(GFP_NOIO);
	if (!zc->metadata_page) {
		ti->error = "Failed to allocate metadata page";
		ret = -ENOMEM;
		goto err_destroy_kcopyd_client;
	}
	zc->metadata = page_address(zc->metadata_page);
	mutex_init(&zc->metadata_mtx);

	if (zbon_read_state(zc)) {
		DMERR("Failed to recover state from metadata block\n");
	}

	ti->flush_supported = 1;
	ti->num_flush_bios = 1;
	ti->num_discard_bios = 1;
	ti->num_secure_erase_bios = 1;
	ti->num_write_zeroes_bios = 1;
	ti->per_io_data_size = sizeof(struct zbon_bioctx);
	ti->len = zc->nr_zones * zc->zone_nr_sectors;
	ti->emulate_zone_append = true;
	ti->private = zc;


	DMINFO("(%s): Target device: %lu zones, %lu active, size %lu sectors, minimum write size %d bytes",
			dm_disk(md)->disk_name, zc->nr_zones, zc->max_active_zones,
			(unsigned long)ti->len, bdev_io_min(zc->bdev));


	return 0;

err_destroy_kcopyd_client:
	dm_kcopyd_client_destroy(zc->kc);
err_destroy_flush_workqueue:
	destroy_workqueue(zc->flush_wq);
err_destroy_sync_workqueue:
	destroy_workqueue(zc->sync_wq);
err_bioset_exit:
	bioset_exit(&zc->bio_set);
err_free_buffers:
	kfree(zc->buffers);
err_free_buffer_bits:
	kfree(zc->buffer_bits);
err_free_zones:
	for (i = 0; i < zc->nr_zones; i++)
		kfree(xa_load(&zc->zones,i));
	xa_destroy(&zc->zones);
err_put_devices:
	dm_put_device(ti, zc->dev);
	dm_put_device(ti, zc->cache_dev);
err_free_zc:
	kfree(zc);
	return ret;
}

static void zbon_dtr(struct dm_target *ti)
{
	struct zbon_c *zc = ti->private;
	int i;

	destroy_workqueue(zc->flush_wq);
	dm_kcopyd_client_destroy(zc->kc);

	if (zbon_store_state(zc)) {
		DMERR("Failed to store state in metadata block");
	}

	bioset_exit(&zc->bio_set);
	dm_put_device(ti, zc->dev);
	dm_put_device(ti, zc->cache_dev);

	for (i = 0; i < zc->nr_zones; i++)
		kfree(xa_load(&zc->zones, i));
	xa_destroy(&zc->zones);

	__free_pages(zc->metadata_page, 0);
	kfree(zc->buffers);
	kfree(zc->buffer_bits);
	kfree(zc);
}

static inline struct zbon_zone *zbon_get_zone(sector_t sec, struct zbon_c *zc) {
	return xa_load(&zc->zones, sec / zc->zone_nr_sectors);
}

static void zbon_zone_op_endio(struct bio *clone)
{
	struct zbon_bioctx *ctx = clone->bi_private;
	blk_status_t status = clone->bi_status;
	struct bio *bio = ctx->bio;
	struct zbon_c *zc = ctx->zc;
	struct zbon_zone *z;
	unsigned long *done = ctx->done;
	unsigned long flags;


	z = zbon_get_zone(bio->bi_iter.bi_sector, zc);
	spin_lock_irqsave(&z->lock, flags);
	if (zbon_update_zone_state(bio, z, zc))
		DMERR("There was an error updating internal zone state");

	spin_unlock_irqrestore(&z->lock, flags);

	bio->bi_status = status;
	bio_put(clone);
	bio_advance(bio, bio->bi_iter.bi_size);

	if (unlikely(bio->bi_opf & REQ_FUA) ||
		bio_op(bio) == REQ_OP_ZONE_FINISH ||
		bio_op(bio) == REQ_OP_ZONE_RESET) {
		zbon_queue_sync_work(bio, &zc->postsync_bios, zc);
	} else {
		bio_endio(bio);
	}

	clear_bit_unlock(1, done);
	smp_mb__after_atomic();
	wake_up_bit(done, 1);
}

static int zbon_queue_deferred_work(int type, struct bio *bio, struct zbon_zone *z, struct zbon_c *zc) {
	struct bio *clone;
	struct zbon_bioctx *bioctx;
	struct zbon_deferred_work *dw;
	struct zbon_zone_workitem *wi;
	unsigned long flags;

	dw = kzalloc(sizeof(struct zbon_deferred_work), GFP_NOIO);
	if (!dw) {
		return -ENOMEM;
	}

	wi = kzalloc(sizeof(struct zbon_zone_workitem), GFP_NOIO);
	if (!wi) {
		kfree(dw);
		return -ENOMEM;
	}

	INIT_WORK(&dw->work, zbon_deferred_work);

	dw->zc = zc;
	dw->zone = z;

	wi->type = type;

	switch (type) {
	case DEFERRED_FLUSH:
		wi->bio = NULL;
		break;
	case DEFERRED_FULL:
		wi->bio = bio;
		break;
	case DEFERRED_ZONE_OP:
		clone = bio_alloc_clone(zc->dev->bdev, bio, GFP_NOIO, &zc->bio_set);
		if (!clone) {
			kfree(dw);
			kfree(wi);
			return -ENOMEM;
		}

		clone->bi_iter.bi_sector = bio->bi_iter.bi_sector;
		clone->bi_iter.bi_size = bio_sectors(bio) << SECTOR_SHIFT;
		clone->bi_end_io = zbon_zone_op_endio;

		bioctx = dm_per_bio_data(bio, sizeof(struct zbon_bioctx));
		bioctx->bio = bio;
		bioctx->zc = zc;
		bioctx->done = NULL;
		clone->bi_private = bioctx;

		wi->bio = clone;

		break;
	default:
		kfree(dw);
		kfree(wi);
		return -EINVAL;
	}

	spin_lock_irqsave(&z->lock, flags);
	list_add_tail(&wi->list, &z->work_list);
	spin_unlock_irqrestore(&z->lock, flags);

	queue_work(zc->flush_wq, &dw->work);

	return 0;
}

static void zbon_clone_endio(struct bio *clone)
{
	struct zbon_bioctx *ctx = clone->bi_private;
	blk_status_t status = clone->bi_status;
	struct bio *bio = ctx->bio;
	struct zbon_c *zc = ctx->zc;
	bool full = false;
	unsigned long flags;

	bio->bi_status = status;
	if (bio_op(bio) == REQ_OP_WRITE && status == BLK_STS_OK) {
		struct zbon_zone *z;

		z = zbon_get_zone(bio->bi_iter.bi_sector, zc);
		spin_lock_irqsave(&z->lock, flags);
		z->blkz.wp += bio_sectors(bio);
		if (z->blkz.wp ==  z->blkz.start + z->blkz.capacity)
			full = true;
		spin_unlock_irqrestore(&z->lock, flags);

		if (full) {
			/* Update zone state after flushing the buffer */
			zbon_queue_deferred_work(DEFERRED_FULL, bio, z, zc);
		} else {
			zbon_queue_deferred_work(DEFERRED_FLUSH, NULL, z, zc);
		}

		if (atomic_read(&zc->sectors_to_flush) > zc->throttle_limit) {
			int overshoot = atomic_read(&zc->sectors_to_flush) - zc->throttle_limit;
			if (overshoot > 0) {
				// TODO: turn the busy waiting into a deferred bio endio
				udelay(overshoot);
			}
		}
	}

	zbon_buffer_put(ctx->buffer, zc);
	bio_put(clone);

	/* We'll complete the bio after flushing if we filled the zone */
	if (!full) {
		bio_advance(bio, bio->bi_iter.bi_size);

		if (unlikely(bio->bi_opf & REQ_FUA)) {
			zbon_queue_sync_work(bio, &zc->postsync_bios, zc);
		} else {
			bio_endio(bio);
		}
	}
}

static int zbon_submit_bio_to_cache(struct bio *bio, struct zbon_zone *z,
				   struct zbon_buffer *buffer, struct zbon_c *zc) {
	struct zbon_bioctx *bioctx =
		dm_per_bio_data(bio, sizeof(struct zbon_bioctx));
	struct bio *clone;

	clone = bio_alloc_clone(zc->dev->bdev, bio, GFP_NOIO, &zc->bio_set);
	if (!clone)
		return DM_MAPIO_KILL;

	bioctx->bio = bio;
	bioctx->zc = zc;
	bioctx->buffer = buffer;

	clone->bi_iter.bi_sector = bio->bi_iter.bi_sector - z->blkz.start + buffer->start;
	clone->bi_iter.bi_size = bio_sectors(bio) << SECTOR_SHIFT;
	clone->bi_end_io = zbon_clone_endio;
	clone->bi_private = bioctx;
	bio_set_dev(clone, zc->cache_bdev);

	/* We need to do a metada sync on REQ_PREFLUSHES and on the first write
	 * to store information about the allocated buffer */
	if (unlikely(bio->bi_opf & REQ_PREFLUSH) ||
	    (bio->bi_iter.bi_sector == z->blkz.start && bio_op(bio) == REQ_OP_WRITE))
		return zbon_queue_sync_work(clone, &zc->presync_bios, zc);

	submit_bio_noacct(clone);

	return DM_MAPIO_SUBMITTED;
}

static int zbon_handle_io(struct bio *bio, struct zbon_c *zc) {
	struct zbon_zone *z;
	struct zbon_buffer *buffer = NULL;
	bool submit_to_cache = false;
	int ret = 0;
	unsigned long flags;

	if (bio_sectors(bio) == 0) {
		bio_set_dev(bio, zc->bdev);
		return DM_MAPIO_REMAPPED;
	}

	if (bio_op(bio) == REQ_OP_WRITE) {
		atomic_add(bio_sectors(bio), &zc->sectors_to_flush);
	}

	z = zbon_get_zone(bio->bi_iter.bi_sector, zc);
	if (z == NULL)
		return DM_MAPIO_KILL;

	spin_lock_irqsave(&z->lock, flags);

	if (z->buffer != NULL) {
		submit_to_cache = true;
	} else if (bio_op(bio) == REQ_OP_WRITE) {
		ret = zbon_buffer_allocate(z, zc);
		if (ret) {
			spin_unlock_irqrestore(&z->lock, flags);
			return DM_MAPIO_KILL;
		}
		submit_to_cache = true;
	}

	if (bio_op(bio) == REQ_OP_WRITE &&
	    (z->blkz.cond == BLK_ZONE_COND_CLOSED ||
	     z->blkz.cond == BLK_ZONE_COND_EMPTY)) {
		z->blkz.cond = BLK_ZONE_COND_IMP_OPEN;
	}

	/* Check that writes are at the write pointer and that the zone is not full */
	if (bio_op(bio) == REQ_OP_WRITE &&
	    (z->blkz.wp != bio->bi_iter.bi_sector || z->blkz.cond == BLK_ZONE_COND_FULL)) {
		ret  = DM_MAPIO_KILL;
	}

	if (submit_to_cache) {
		zbon_buffer_get(z->buffer);
		buffer = z->buffer;
	}

	spin_unlock_irqrestore(&z->lock, flags);

	if (ret)
		return ret;

	if (submit_to_cache) {
		return zbon_submit_bio_to_cache(bio, z, buffer, zc);
	} else {
		bio_set_dev(bio, zc->bdev);
		return DM_MAPIO_REMAPPED;
	}
}

static int zbon_handle_zone_op(struct bio *bio, struct zbon_c *zc)
{
	struct zbon_zone *z;
	int ret;

	z = zbon_get_zone(bio->bi_iter.bi_sector, zc);
	if (z == NULL) {
		return DM_MAPIO_KILL;
	}

	if (zbon_queue_deferred_work(DEFERRED_ZONE_OP, bio, z, zc))
		ret = DM_MAPIO_KILL;
	else
		ret = DM_MAPIO_SUBMITTED;

	return ret;
}

static int zbon_handle_bio(struct bio *bio, struct zbon_c *zc)
{
	int ret;

	switch (bio_op(bio)) {
	case REQ_OP_READ:
	case REQ_OP_WRITE:
	case REQ_OP_DISCARD:
	case REQ_OP_WRITE_ZEROES:
		ret = zbon_handle_io(bio, zc);
		break;
	case REQ_OP_ZONE_OPEN:
	case REQ_OP_ZONE_CLOSE:
	case REQ_OP_ZONE_FINISH:
	case REQ_OP_ZONE_RESET:
		ret = zbon_handle_zone_op(bio, zc);
		break;
	default:
		DMERR("Unsupported BIO operation 0x%x", bio_op(bio));
		ret = DM_MAPIO_KILL;
	}

	return ret;
}

static int zbon_map(struct dm_target *ti, struct bio *bio)
{
	struct zbon_c *zc = ti->private;
	int ret;

	ret = zbon_handle_bio(bio, zc);

	if (ret == DM_MAPIO_REMAPPED && unlikely(bio->bi_opf & REQ_PREFLUSH)) {
		return zbon_queue_sync_work(bio, &zc->presync_bios, zc);
	}

	return ret;
}

static void zbon_status(struct dm_target *ti, status_type_t type,
			  unsigned int status_flags, char *result, unsigned int maxlen)
{
	struct zbon_c *zc = ti->private;
	size_t sz = 0;

	switch (type) {
	case STATUSTYPE_INFO:
		result[0] = '\0';
		break;

	case STATUSTYPE_TABLE:
		DMEMIT("%s", zc->dev->name);
		break;

	case STATUSTYPE_IMA:
		DMEMIT_TARGET_NAME_VERSION(ti->type);
		DMEMIT(",device_name=%s;", zc->dev->name);
		break;
	}
}

static int zbon_prepare_ioctl(struct dm_target *ti, struct block_device **bdev)
{
	struct zbon_c *zc = ti->private;
	struct dm_dev *dev = zc->dev;

	*bdev = dev->bdev;

	return 0;
}

static int zbon_report_zones(struct dm_target *ti,
		struct dm_report_zones_args *args, unsigned int nr_zones)
{
	struct zbon_c *zc = ti->private;
	unsigned long int start;
	struct blk_zone blkz;
	struct zbon_zone *z;
	long unsigned int i;
	int ret = 0;
	unsigned long flags;

	start = args->next_sector / zc->zone_nr_sectors;

	for (i = start; i < start + nr_zones; i++) {
		z = xa_load(&zc->zones, i);
		if (!z) {
			break;
		}

		spin_lock_irqsave(&z->lock, flags);
		memcpy(&blkz, &z->blkz, sizeof(struct blk_zone));
		spin_unlock_irqrestore(&z->lock, flags);

		ret = args->orig_cb(&blkz, i - start, args->orig_data);
		if (ret) {
			break;
		}
		args->next_sector = blkz.start + blkz.len;
		args->zone_idx++;
	}

	if (ret)
		return ret;

	return 0;
}

static int zbon_iterate_devices(struct dm_target *ti,
				  iterate_devices_callout_fn fn, void *data)
{
	struct zbon_c *zc = ti->private;

	return fn(ti, zc->dev, 0, ti->len, data);
}


static struct target_type zbon_target = {
	.name   = "zbon",
	.version = {1, 0, 0},
	.features = DM_TARGET_PASSES_INTEGRITY | DM_TARGET_NOWAIT |
		    DM_TARGET_ZONED_HM | DM_TARGET_PASSES_CRYPTO,
	.report_zones = zbon_report_zones,
	.module = THIS_MODULE,
	.ctr    = zbon_ctr,
	.dtr    = zbon_dtr,
	.map    = zbon_map,
	.status = zbon_status,
	.prepare_ioctl = zbon_prepare_ioctl,
	.iterate_devices = zbon_iterate_devices,
};
module_dm(zbon)

MODULE_DESCRIPTION(DM_NAME " target for buffering zoned block devices");
MODULE_AUTHOR("Hans Holmberg <hans.holmberg@wdc.com>");
MODULE_LICENSE("GPL");
