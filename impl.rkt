#lang racket


(provide == succeed fail disj2 conj2 disj conj
         defrel run run* fresh conde conda condu)


(define var
  (lambda (name)
    (vector name)))


(define var?
  (lambda (x)
    (vector? x)))


(define empty-s '())


(define assv
  (lambda (var subs)
    (cond
      [(null? subs) #f]
      [(eq? var (caar subs))
       (cdar subs)]
      [else
       (assv var (cdr subs))])))


(define walk
  (lambda (var subs)
    (let ([a (assv var subs)])
      (if (boolean? a)
          var
          (if (var? a)
              (walk a subs)
              a)))))


(define occurs?
  (lambda (var value subs)
    (set! value (walk value subs))
    (cond
      [(var? value) (eq? var value)]
      [(pair? value)
       (or (occurs? var (car value) subs)
           (occurs? var (cdr value) subs))]
      [else #f])))


(define ext-s
  (lambda (var value subs)
    (if (occurs? var value subs)
        #f
        (cons (cons var value) subs))))


(define unify
  (lambda (u v subs)
    (set! u (walk u subs))
    (set! v (walk v subs))
    (cond
      [(eq? u v) subs]
      [(var? u) (ext-s u v subs)]
      [(var? v) (ext-s v u subs)]
      [(and (pair? u) (pair? v))
       (set! subs (unify (car u) (car v) subs))
       (if (boolean? subs)
           #f
           (unify (cdr u) (cdr v) subs))]
      [else #f])))


(define ==
  (lambda (u v)
    (lambda (subs)  ;; return a stream
      (set! subs (unify u v subs))
      (if (boolean? subs)
          '()
          (list subs)))))


;; return a stream
(define succeed
  (lambda (subs) 
    (list subs)))


;; return a stream
(define fail
  (lambda (subs)
    '()))


(define append~
  (lambda (stream1 stream2)
    (cond
      [(null? stream1) stream2]
      [(pair? stream1)
       (cons (car stream1)
             (append~ (cdr stream1) stream2))]
      [else
       (lambda ()
         (append~ stream2 (stream1)))])))


(define disj2
  (lambda (g1 g2)
    (lambda (subs)
      (append~ (g1 subs) (g2 subs)))))


(define append-map~
  (lambda (stream g)
    (cond
      [(null? stream) '()]
      [(pair? stream)
       (append~ (g (car stream))
                (append-map~ (cdr stream) g))]
      [else
       (lambda ()
         (append-map~ (stream) g))])))


(define conj2
  (lambda (g1 g2)
    (lambda (subs)
      (append-map~ (g1 subs) g2))))


(define callfresh
  (lambda (name f)
    (f (var name))))


(define reify-name
  (lambda (n)
    (string->symbol
     (string-append "_" (number->string n)))))


(define walk*
  (lambda (var subs)
    (set! var (walk var subs))
    (cond
      [(var? var) var]
      [(pair? var)
       (cons (walk* (car var) subs)
             (walk* (cdr var) subs))]
      [else var])))


(define reify-s
  (lambda (var reifies)
    (set! var (walk var reifies))
    (cond
      [(var? var)
       (let* ([n (length reifies)]
              [rn (reify-name n)])
         (cons (cons var rn) reifies))]
      [(pair? var)
       (set! reifies (reify-s (car var) reifies))
       (reify-s (cdr var) reifies)]
      [else reifies])))


(define reify
  (lambda (var)
    (lambda (subs)
      (let* ([var (walk* var subs)]
             [reifies (reify-s var empty-s)])
        (walk* var reifies)))))


(define take~
  (lambda (n stream)
    (cond
      [(and n (= 0 n)) '()]
      [(null? stream) '()]
      [(pair? stream)
       (cons (car stream)
             (take~ (and n (sub1 n)) (cdr stream)))]
      [else
       (take~ n (stream))])))


(define run-goal
  (lambda (n g)
    (take~ n (g empty-s))))


(define ifte
  (lambda (g1 g2 g3)
    (lambda (subs)
      (let loop ([s (g1 subs)])
        (cond
          [(null? s) (g3 s)]
          [(pair? s) (append-map~ s g2)]
          [else
           (lambda () (loop (s)))])))))


(define once
  (lambda (g)
    (lambda (subs)
      (let loop ([s (g subs)])
        (cond
          [(null? s) '()]
          [(pair? s)
           (cons (car s) '())]
          [else
           (lambda () (loop (s)))])))))


(define-syntax disj
  (syntax-rules ()
    [(disj) fail]
    [(disj g) g]
    [(disj g0 g ...) (disj2 g0 (disj g ...))]))


(define-syntax conj
  (syntax-rules ()
    [(conj) succeed]
    [(conj g) g]
    [(conj g0 g ...) (conj2 g0 (conj g ...))]))


(define-syntax defrel
  (syntax-rules ()
    [(defrel (name x ...) g ...)
     (define name
       (lambda (x ...)
         (lambda (subs)
           (lambda ()
             ((conj g ...) subs)))))]))


(define-syntax run
  (syntax-rules ()
    [(run n (x0 x ...) g ...)
     (run n q
          (fresh (x0 x ...)
                 (== (list x0 x ...) q)
                 g ...))]
    [(run n q g ...)
     (let ([q (var 'q)])
       (map (reify q)
            (run-goal n (conj g ...))))]))


(define-syntax run*
  (syntax-rules ()
    [(run* q g ...) (run #f q g ...)]))


(define-syntax fresh
  (syntax-rules ()
    [(fresh () g ...) (conj g ...)]
    [(fresh (x0 x ...) g ...)
     (callfresh
      'x0
      (lambda (x0)
        (fresh (x ...) g ...)))]))


(define-syntax conde
  (syntax-rules ()
    [(conde (g ...) ...)
     (disj (conj g ...) ...)]))


(define-syntax conda
  (syntax-rules ()
    [(conda (g0 g ...))
     (conj g0 g ...)]
    [(conda (g0 g ...) ln ...)
     (ifte g0 (conj g ...) (conda ln ...))]))


(define-syntax condu
  (syntax-rules ()
    [(condu (g0 g ...) ...)
     (conda ((once g0) g ...) ...)]))