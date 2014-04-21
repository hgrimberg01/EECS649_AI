#lang racket
(require data/heap)
(struct node (action state predecessor g h f))

(define (node-<= a b)
  (<= (node-f a) (node-f b)))



; Utility function to find the index of an item in the list
(define (index-of haystack needle)
  (let finder ((haystack haystack) (i 0))
    (cond [(empty? haystack) -1]
          [(eq? (car haystack) needle) i]
          [else (finder (cdr haystack) (+ 1 i))]
          
          )
    
    ))

; Returns the cartesian coordinates as a (Y X) pair given 
; a state (as nested lists '((1 2 3) (4 5 5)).
(define (compute-xy-cord state needle)
  (define flat (flatten state))
  (define local  (index-of flat needle))
  
  (list (floor (/ local 3)) (modulo local 3))
  
  
  )


; Checks if the coordiante is something that can exist (ie 
; no negatives. 

(define (valid-cord? pair)
  (cond [ (or (> (car pair) 2) (< (car pair) 0)) #f ]
        [(or (> (second pair) 2) (< (second pair) 0)) #f]
        
        [else #t]
        
        ))


; Finds the candidate pairs surrounding a given coordinate
; Also returns the opposite action of the blank tile (aka 0)
; NOTE: Only returns valid pairs
(define (find-candidate-cord pair)
  (define x (second pair))
  (define y (car pair))
  (define xn (+ x 1))
  (define yn (+ y 1))
  (define xp (- x 1))
  (define yp (- y 1))
  
  ; UP
  
  (define up (list yp x 'DOWN))
  
  ; DOWN
  
  (define down (list yn x 'UP))
  
  ; LEFT 
  (define left (list y xp 'RIGHT))
  
  ; RIGHT
  (define right (list y xn 'LEFT))
  
  (define final (list up down left right))
  
  (filter valid-cord? final)
  
  )




; Swaps positions of two different coordinates.
; Returns a fresh state consisting of nested lists

(define (swap state f s)
  (define flat (flatten state))
  
  (define firstIndex (coord-to-index f))
  (define secondIndex (coord-to-index s))
  
  (define firstItem (list-ref flat firstIndex))
  (define secondItem (list-ref flat secondIndex))
  
  (define nstate (map (lambda(e)
                        
                        (cond [(eq? e firstItem) secondItem]
                              [(eq? e secondItem) firstItem]
                              [else e]
                              
                              
                              
                              )) flat))
  
  
  
  
  
  (list (take nstate 3) (take (cdddr nstate) 3) (take (cdddr (cdddr nstate)) 3))
  
  )


; Flatten a (Y X) pair to a index of a flattent 2D state.
(define (coord-to-index coord)
  (+ (* (car coord) 3) (second coord))
  )




; This is a goal state
(define goal-state '((1 2 3) (4 5 6) (7 8 0)))



; The move function
(define (move state)
  
  (define z (compute-xy-cord state 0))
  (define pos (find-candidate-cord z))
  (map (lambda(e)  (list (swap state e z) (list (third e)  (coord-to-index e)) 1)
         ) pos))


; Find the sum of the manhattan(taxicab) geometry distances
(define (manhattan state goal)
  (define gflat (flatten goal))
  (define flat (flatten state))
  (define z (compute-xy-cord state 0))
  (define sums (map (lambda(e) (if (not(eq? e 0)) (find-m-dist (compute-xy-cord state e) 
                                                               (compute-xy-cord goal e)) 0)
                      
                      )flat))
  
  (apply + sums)
  
  
  
  )

; Find the  manhattan(taxicab) geometry distance of given (Y X) pairs.
(define (find-m-dist coord1 coord2)
  ( + (abs (- (car coord1) (car coord2)))
      (abs (- (second coord1) (second coord2))))
  )




; Are we there yet?
(define (goal? state ns )
  (equal? state ns)
  )

; Does nothing
(define (null-heuristic state goal)
  0)



(define (a-star-graph-search start goal goal? moves heuristic)
  (define explored (make-hash))
  (define frontier (make-heap (lambda (a b) (node-<= a b))))
  
  (heap-add! frontier (node 'START start 'none 0 (heuristic start goal) (+ (heuristic start goal) 0)))
  (define counter 0)
  (define (inf-loop)
    (define lead (heap-min frontier))
    (heap-remove-min! frontier)
    (cond 
      
      [(goal? goal-state (node-state lead))  ((lambda() (displayln counter) lead))]
      [(empty? frontier) 'NO_SOL]
      [else 
       (hash-set! explored (node-state lead) lead)
       (set! counter (+ counter 1))
       
       (define pmoves (moves (node-state lead)))
       (map(λ(e)
             (hash-ref explored (first e) (lambda()
                                            (define nnode (node (second e) (first e) lead (+ (node-g lead) (third e)) (heuristic (first e) goal)  ( + (heuristic (first e) goal) (+ (node-g lead) (third e)))))  
                                            (heap-add! frontier nnode)))
             )pmoves)
       (inf-loop)
       ]
      
      )
    
    
    
    )
  (inf-loop)
  )

(define bba0 '((6 4 2) (1 5 3) (7 0 8)))
(define bba1 '((6 4 2) (8 5 3) (1 0 7)))
(define bba2 '((6 4 7) (8 5 0) (3 2 1)))
(define bba3 '((8 0 7) (6 5 4) (3 2 1)))
(define bba4 '((1 2 3) (4 5 6) (8 7 0)))




(define  (tile-puzzle start end)
  (define nnode (time (a-star-graph-search start end goal? move manhattan)))
  
  (enode nnode)
  
  )

(define (enode nd [ls '()])
  (cond [(eq? (node-predecessor nd) 'none) (cons (list (node-action nd) (node-state nd) (node-g nd) (node-h nd) (node-f nd)) ls)]
        [else  (enode (node-predecessor nd) (cons  (list (node-action nd) (node-state nd) (node-g nd) (node-h nd) (node-f nd)) ls ))]
        ))

(define  (tile-puzzle-nil-h start end)
  (define nnode (time (a-star-graph-search start end goal? move null-heuristic)))
  
  (enode nnode)
  
  )
(displayln "Manhattan")
(tile-puzzle bba0 goal-state)
(tile-puzzle bba1 goal-state)
(tile-puzzle bba2 goal-state)
(tile-puzzle bba3 goal-state)


(displayln "Nil Heuristic")
(tile-puzzle-nil-h bba0 goal-state)
(tile-puzzle-nil-h bba1 goal-state)
(tile-puzzle-nil-h bba2 goal-state)
(tile-puzzle-nil-h bba3 goal-state)


(displayln "Fail with Manhattan/Null heuristic respectively. Unsolveable")
(tile-puzzle bba4 goal-state)
(tile-puzzle-nil-h bba4 goal-state)
