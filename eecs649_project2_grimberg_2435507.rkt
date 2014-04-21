#lang racket
(require data/heap)
(require racket/trace)


(struct node (action state predecessor g h f))
(define (node-<= a b)
  (<= (node-f a) (node-f b)))



(define axioms2 '(
                  ((=(* x (K))x))
                  ((=(* (K)x)x))
                  ((=(* x(/ x))(K)))
                  ((=(* (/ x)x)(K)))
                  ((=(* x w)v)(¬(=(* x y)u))(¬(=(* y z)w))(¬(=(* u z)v)))
                  ((=(* u z)v)(¬(=(* x y)u))(¬(=(* y z)w))(¬(=(* x w)v)))
                  ((=(* x x)(K)))
                  ((=(* (F)(G))(H)))
                  ))

(define conjs2 '((¬(=(* (G)(F))(H)))))


(define axioms1 '(
                  ((Criminal x) (¬ (American x)) (¬ (Weapon y)) (¬ (Sells x y z)) (¬ (Hostile z)))
                  ((Enemy (nono) (america)))
                  ((Missile (m1)))
                  ((Owns (nono) (m1)))
                  ((Sells (west) x (nono)) (¬(Missile x)) (¬(Owns (nono) x)))
                  ((American (west)))
                  ((Weapon x) (¬ (Missile x)))
                  ((Hostile x) (¬(Hostile (MotherOf x))))
                  
                  ((Hostile x) (¬ (Enemy x (america))))
                  
                  ((Hostile x) (¬(Hostile (FatherOf x))))
                  ))

(define conjs1 '((¬ (Criminal (west)))))

; Utility function to find the index of an item in the list
(define (index-of haystack needle)
  (let finder ((haystack haystack) (i 0))
    (cond [(empty? haystack) -1]
          [(equal? haystack needle) i]
          [(equal? (car haystack) needle) i]
          [else (finder (cdr haystack) (+ 1 i))] 
          )
    ))

; This is a goal state
(define goal-state '() )



; The move function
(define (move state)
  (display 'a)
  )


; Are we there yet?
(define (goal? state ns )
  (equal? state ns)
  )

; Does nothing
(define (null-heuristic state goal)
  0)







(define (a-star-graph-search startStates goal goal? moves heuristic)
  (define explored (make-hash))
  (define frontier (make-heap (lambda (a b) (node-<= a b))))
  (map (lambda y  (heap-add! frontier (node '() y 'none 0 (heuristic y goal) (+ (heuristic y goal) 0)))
         )startStates)
  (define counter 0)
  (define (inf-loop)
    
    (define lead (heap-min frontier))
    (heap-remove-min! frontier)
    
    (cond 
      
      [(goal? goal (node-state lead))  ((lambda() (displayln counter) lead))]
      [(empty? frontier) 'NO_SOL]
      [else 
       (hash-set! explored (node-state lead) lead)
       (set! counter (+ counter 1))
       
       
       (define pmoves (moves (node-state lead)))
       
       (map(λ a
             (define e (car a))
             (hash-ref explored (first e) (lambda ()
                                            (define nnode (node (second e) (car (first e)) lead (+ (node-g lead) (third e)) (heuristic (first e) goal)  ( + (heuristic (first e) goal) (+ (node-g lead) (third e)))))  
                                            (heap-add! frontier nnode)))
             )pmoves)
       (inf-loop)
       ]
      
      )
    
    
    
    )
  (inf-loop)
  )

; See http://stackoverflow.com/questions/765484/how-to-write-a-scheme-function-that-takes-two-lists-and-returns-four-lists
(define (union a b) 
  (cond ((null? b) a) 
        ((element? (car b) a) 
         (union a (cdr b))) 
        (#t (union (cons (car b) a) (cdr b)))))

(define (element? a b)
  (memq a b))


(define (bound? x t)
  (if (not (pair? x)) #f
  (assoc x t)))

(define (value x t)
  (cdr (assoc x t)))


(define (occur? v x t)
  
  (cond 
    [(and (symbol? x) (bound? x t)) (occur? v (value x t) t)]
    [(equal? v x) #t]
    [(symbol? v) #f]
    [else (ormap (lambda x (occur? v x t) (cdr x)))]))

(define (unify x y t)
  
  (cond
    [(equal? t #f) #f]
    [(equal? x y) (list t)]
    [(and (symbol? x) (bound? x t)) (unify  (value x t) y t)]
    [(and (symbol? y) (bound? y t)) (unify  x (value y t) t )]
    
    [(symbol? x) (if (occur? x y t) #f (cons (cons y x) t))]
    [(symbol? y) (if (occur? y x t) #f (cons (cons y x) t))]
    
    
    [(not (= (length x)(length y))) #f]
    [(not (and (pair? x) (pair? y)) ) #f]
    [(not (equal? (car x)(car y))) #f]
    
    
    [else  (foldl unify t (cdr x) (cdr y))]))


(define (instantiate x t)
  
  (cond 
    
    [(and (symbol? x) (bound? x t)) (instantiate (value x t) t)]
    [(symbol? x) x]
    [else (map (lambda p (instantiate (car p) t)) x)]))

(define (freevarsin x)
  (cond 
    [(symbol? x) (list x)]
    [(equal? (length x) 1) '()]
    [else (foldr union '() (map (lambda p (freevarsin (car p))) (cdr x)))]))




(define (rename ids body)
  (cond
    [(equal? ids '()) body]
    [else (instantiate body (map (lambda p (cons (car p) (gensym (car p)))) ids))]))

; Resolve Function
(define (doresolve ngc dhc)
  
  ; Rename
  (define step1 (rename (freevarsin dhc) dhc))
  
  ; Try unifying
  (define step2 (unify (cadar ngc) (car step1) '()))
  (cond 
    [(equal? step2 #f)  #f]
    [else (cons (union (instantiate (cdr ngc) step2) (instantiate (cdr step1)  step2)) dhc)])
  )

(define (resolve negc hornc)
  (define newc (rename (freevarsin hornc) hornc))
  (define bind (unify (cadar negc) (car newc) '()))
  (cond
    ((equal? bind #f) #f)
    (else (list (union (instantiate (cdr negc) bind ) (instantiate (cdr newc) bind )) hornc) )))



(define (find-possible kb s)
  (map (lambda p
         (define d (doresolve s (car p) ))
         (cond [(not (equal? d #f)) (list d p 1)]
               [else #f]
               
               )) kb)
  )

(define (my-move-func kb s)
  (filter (lambda e  (cond [(equal? (first e) #f) #f][else #t])) (find-possible kb s)))




(define (dumb-heuristic s goal)
  (length s))



(define (deduce start-state kb)
  (define (move s)
    (my-move-func kb s))
  
  (define end-node (a-star-graph-search start-state goal-state goal? move dumb-heuristic))
  
  
  (define (enode nd [ls '()])
    (cond [(eq? (node-predecessor nd) 'none) (cons (list (node-action nd) (node-state nd) (node-g nd) (node-h nd) (node-f nd)) ls)]
          [else  (enode (node-predecessor nd) (cons  (list (node-action nd) (node-state nd) (node-g nd) (node-h nd) (node-f nd)) ls ))]
          ))
  
  (define (enode-p nd [step 0] )
    
    (if (empty? nd) 'DONE ((lambda ()
                             (display "Step Num:")
                             (displayln step)
                             (displayln (first nd))
                             (display "--->")
                             (displayln (cdr nd))
                             (enode-p (cdr nd) (+ step 1))))))
  
  
  
  (define rrev (enode end-node))
  (enode-p rrev)
  
  
  )

(deduce conjs2 axioms2)

(deduce conjs1 axioms1)

