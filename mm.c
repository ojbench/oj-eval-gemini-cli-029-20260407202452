#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define PRED_PTR(bp) ((char *)(bp))
#define SUCC_PTR(bp) ((char *)(bp) + WSIZE)

#define PRED(bp) (*(unsigned int *)(PRED_PTR(bp)))
#define SUCC(bp) (*(unsigned int *)(SUCC_PTR(bp)))

#define OFFSET(bp) ((unsigned int)((long)(bp) - (long)heap_listp))
#define ADDRESS(offset) ((void *)((long)heap_listp + (offset)))

#define LIST_MAX 20

static char *heap_listp = 0;
static unsigned int segregated_free_lists[LIST_MAX];

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *place(void *bp, size_t asize);
static void insert_node(void *bp, size_t size);
static void delete_node(void *bp);

int mm_init(void) {
    int i;
    for (i = 0; i < LIST_MAX; i++) {
        segregated_free_lists[i] = 0;
    }

    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void insert_node(void *bp, size_t size) {
    int list = 0;
    size_t searchsize = size;

    while ((list < LIST_MAX - 1) && (searchsize > 1)) {
        searchsize >>= 1;
        list++;
    }

    unsigned int search_ptr = segregated_free_lists[list];
    unsigned int insert_ptr = 0;

    while ((search_ptr != 0) && (size > GET_SIZE(HDRP(ADDRESS(search_ptr))))) {
        insert_ptr = search_ptr;
        search_ptr = SUCC(ADDRESS(search_ptr));
    }

    if (search_ptr != 0) {
        if (insert_ptr != 0) {
            PUT(SUCC_PTR(bp), search_ptr);
            PUT(PRED_PTR(bp), insert_ptr);
            PUT(PRED_PTR(ADDRESS(search_ptr)), OFFSET(bp));
            PUT(SUCC_PTR(ADDRESS(insert_ptr)), OFFSET(bp));
        } else {
            PUT(SUCC_PTR(bp), search_ptr);
            PUT(PRED_PTR(bp), 0);
            PUT(PRED_PTR(ADDRESS(search_ptr)), OFFSET(bp));
            segregated_free_lists[list] = OFFSET(bp);
        }
    } else {
        if (insert_ptr != 0) {
            PUT(SUCC_PTR(bp), 0);
            PUT(PRED_PTR(bp), insert_ptr);
            PUT(SUCC_PTR(ADDRESS(insert_ptr)), OFFSET(bp));
        } else {
            PUT(SUCC_PTR(bp), 0);
            PUT(PRED_PTR(bp), 0);
            segregated_free_lists[list] = OFFSET(bp);
        }
    }
}

static void delete_node(void *bp) {
    int list = 0;
    size_t size = GET_SIZE(HDRP(bp));

    while ((list < LIST_MAX - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }

    unsigned int pred = PRED(bp);
    unsigned int succ = SUCC(bp);

    if (pred != 0) {
        if (succ != 0) {
            PUT(SUCC_PTR(ADDRESS(pred)), succ);
            PUT(PRED_PTR(ADDRESS(succ)), pred);
        } else {
            PUT(SUCC_PTR(ADDRESS(pred)), 0);
        }
    } else {
        if (succ != 0) {
            PUT(PRED_PTR(ADDRESS(succ)), 0);
            segregated_free_lists[list] = succ;
        } else {
            segregated_free_lists[list] = 0;
        }
    }
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        insert_node(bp, size);
        return bp;
    } else if (prev_alloc && !next_alloc) {
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        delete_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    insert_node(bp, size);
    return bp;
}

void *malloc(size_t size) {
    size_t asize;
    size_t extendsize;
    char *bp = NULL;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    int list = 0;
    size_t searchsize = asize;
    while (list < LIST_MAX) {
        if ((list == LIST_MAX - 1) || ((searchsize <= 1) && (segregated_free_lists[list] != 0))) {
            unsigned int search_ptr = segregated_free_lists[list];
            while ((search_ptr != 0) && (asize > GET_SIZE(HDRP(ADDRESS(search_ptr))))) {
                search_ptr = SUCC(ADDRESS(search_ptr));
            }
            if (search_ptr != 0) {
                bp = ADDRESS(search_ptr);
                break;
            }
        }
        searchsize >>= 1;
        list++;
    }

    if (bp == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);
        if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
            return NULL;
    }

    bp = place(bp, asize);
    return bp;
}

static void *place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    size_t remainder = csize - asize;

    delete_node(bp);

    if (remainder >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        void *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(remainder, 0));
        PUT(FTRP(next_bp), PACK(remainder, 0));
        insert_node(next_bp, remainder);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    return bp;
}

void free(void *bp) {
    if (bp == 0)
        return;
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

void *realloc(void *ptr, size_t size) {
    size_t oldsize;
    void *newptr;

    if (size == 0) {
        free(ptr);
        return 0;
    }

    if (ptr == NULL) {
        return malloc(size);
    }

    size_t asize;
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    oldsize = GET_SIZE(HDRP(ptr));
    if (oldsize >= asize) {
        return ptr;
    }

    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));

    if (!next_alloc && (oldsize + next_size >= asize)) {
        delete_node(NEXT_BLKP(ptr));
        PUT(HDRP(ptr), PACK(oldsize + next_size, 1));
        PUT(FTRP(ptr), PACK(oldsize + next_size, 1));
        return ptr;
    }

    newptr = malloc(size);
    if (!newptr) {
        return 0;
    }

    memcpy(newptr, ptr, oldsize - DSIZE);
    free(ptr);

    return newptr;
}

void *calloc(size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    if (newptr) {
        memset(newptr, 0, bytes);
    }
    return newptr;
}

void mm_checkheap(int verbose) {
    (void)verbose;
}