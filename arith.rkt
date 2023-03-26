#lang racket


(require "impl.rkt")


(defrel (caro p a)
  (fresh (d)
         (== (cons a d) p)))


(defrel (cdro p d)
  (fresh (a)
         (== (cons a d) p)))


(defrel (conso a d p)
  (== (cons a d) p))


(defrel (nullo x)
  (== '() x))


(defrel (pairo p)
  (fresh (a d)
         (== (cons a d) p)))


(defrel (singletono l)
  (fresh (a)
         (== (list a) l)))


(defrel (listo l)
  (conde
   [(nullo l)]
   [(fresh (d)
           (cdro l d)
           (listo d))]))


(defrel (lolo l)
  (conde
   [(nullo l)]
   [(fresh (a d)
           (== (cons a d) l)
           (listo a)
           (lolo d))]))


(defrel (loso l)
  (conde
   [(nullo l)]
   [(fresh (a d)
           (== (cons a d) l)
           (singletono a)
           (loso d))]))


(defrel (membero x l)
  (fresh (a d)
         (== (cons a d) l)
         (conde
          [(== x a)]
          [(membero x d)])))


(defrel (proper-membero x l)
  (fresh (a d)
         (== (cons a d) l)
         (conde
          [(== x a)
           (listo d)]
          [(proper-membero x d)])))


(defrel (appendo l1 l2 out)
  (conde
   [(nullo l1) (== l2 out)]
   [(fresh (a d res)
           (== (cons a d) l1)
           (==  (cons a res) out)
           (appendo d l2 res))]))


(defrel (memo x l out)
  (conde
   [(caro l x) (== l out)]
   [(fresh (d)
           (cdro l d)
           (memo x d out))]))


(defrel (removeo x l out)
  (conde
   [(nullo l) (== '() out)]
   [(conso x out l)]
   [(fresh (a d res)
           (conso a d l)
           (conso a res out)
           (removeo x d res))]))


(defrel (bit-xoro x y z)
  (conde
   [(== 0 x) (== 0 y) (== 0 z)]
   [(== 0 x) (== 1 y) (== 1 z)]
   [(== 1 x) (== 0 y) (== 1 z)]
   [(== 1 x) (== 1 y) (== 0 z)]))


(defrel (bit-ando x y z)
  (conde
   [(== 0 x) (== 0 y) (== 0 z)]
   [(== 0 x) (== 1 y) (== 0 z)]
   [(== 1 x) (== 0 y) (== 0 z)]
   [(== 1 x) (== 1 y) (== 1 z)]))


(defrel (half-addero x y z1 z2)
  (bit-xoro x y z1)
  (bit-ando x y z2))


(defrel (full-addero b x y z1 z2)
  (fresh (w xy wz)
         (half-addero x y w xy)
         (half-addero w b z1 wz)
         (bit-xoro xy wz z2)))


(define build-num
  (lambda (n)
    (cond
      [(= 0 n) '()]
      [(even? n)
       (cons 0 (build-num (/ n 2)))]
      [else
       (cons 1 (build-num (/ (- n 1) 2)))])))


(defrel (poso n)
  (fresh (a d)
         (== (cons a d) n)))


(defrel (>1o n)
  (fresh (a ad dd)
         (== (cons a (cons ad dd)) n)))


(defrel (addero b x y z)
  (conde
   [(== 0 b) (== '() x) (== y z)]
   [(== 0 b) (poso x) (== '() y) (== x z)]
   [(== 1 b) (== '() x) (addero 0 '(1) y z)]
   [(== 1 b) (poso x) (== '() y) (addero 0 x '(1) z)]
   [(== '(1) x) (== '(1) y)
                (fresh (a c)
                       (== (list a c) z)
                       (full-addero b 1 1 a c))]
   [(== '(1) x) (gen-addero b x y z)]
   [(>1o x) (== '(1) y) (>1o z) (addero b '(1) x z)]
   [(>1o x) (gen-addero b x y z)]))


(defrel (gen-addero b x y z)
  (fresh (x1 x2 y1 y2 z1 z2 a)
         (conso x1 x2 x)
         (conso y1 y2 y) (poso y2)
         (conso z1 z2 z)
         (full-addero b x1 y1 z1 a)
         (addero a x2 y2 z2)))


(defrel (+o x y z)
  (addero 0 x y z))


(defrel (-o z x y)
  (+o x y z))


(defrel (lengtho l n)
  (conde
   [(nullo l) (== '() n)]
   [(fresh (d res)
           (cdro l d)
           (+o '(1) res n)
           (lengtho d res))]))


(defrel (*o x y z)
  (conde
   [(== '() x) (== '() z)]
   [(poso x) (== '() y) (== '() z)]
   [(== '(1) x) (poso y) (== y z)]
   [(>1o x) (== '(1) y) (== x z)]
   [(fresh (x1 z1)
           (conso 0 x1 x) (poso x1)
           (>1o y)
           (conso 0 z1 z) (poso z1)
           (*o x1 y z1))]
   [(fresh (x1 y1)
           (conso 1 x1 x) (poso x1)
           (conso 0 y1 y) (poso y1)
           (*o y x z))]
   [(fresh (x1 y1)
           (conso 1 x1 x) (poso x1)
           (conso 1 y1 y) (poso y1)
           (odd-*o x1 x y z))]))


(defrel (odd-*o x1 x y z)
  (fresh (q)
         (bound-*o q z x y)
         (*o x1 y q)
         (+o (cons 0 q) y z)))


(defrel (bound-*o q p n m)
  (conde
   [(== '() q) (poso p)]
   [(fresh (a0 a1 a2 a3 x y z)
           (conso a0 x q)
           (conso a1 y p)
           (conde
            [(== '() n) (conso a2 z m) (bound-*o x y z '())]
            [(conso a3 z n) (bound-*o x y z m)]))]))


(defrel (=lo x y)
  (conde
   [(== '() x) (== '() y)]
   [(== '(1) x) (== '(1) y)]
   [(fresh (x1 x2 y1 y2)
           (conso x1 x2 x) (poso x2)
           (conso y1 y2 y) (poso y2)
           (=lo x2 y2))]))


(defrel (<lo x y)
  (conde
   [(== '() x) (poso y)]
   [(== '(1) x) (>1o y)]
   [(fresh (x1 x2 y1 y2)
           (conso x1 x2 x) (poso x2)
           (conso y1 y2 y) (poso y2)
           (<lo x2 y2))]))


(defrel (<=lo x y)
  (conde
   [(=lo x y)]
   [(<lo x y)]))


(defrel (<o x y)
  (conde
   [(<lo x y)]
   [(=lo x y)
    (fresh (a)
           (poso a)
           (+o x a y))]))


(defrel (<=o x y)
  (conde
   [(== x y)]
   [(<o x y)]))


(defrel (/o x y q r)
  (conde
   [(<o x y) (== '() q) (== x r)]
   [(== x y) (== '(1) q) (== '() r) (<o r y)]
   [(poso q) (<o y x) (<o r y)
             (n-wider-than-mo x y q r)]))


(defrel (splito n r l h)
  (conde
   [(== '() n) (== '() h) (== '() l)]
   [(fresh (b n1)
           (== (cons 0 (cons b n1)) n)
           (== '() r)
           (conso b n1 h)
           (== '() l))]
   [(fresh (n1)
           (conso 1 n1 n)
           (== '() r)
           (== n1 h)
           (== '(1) l))]
   [(fresh (b n1 a r1)
           (== (cons 0 (cons b n1)) n)
           (conso a r1 r)
           (== '() l)
           (splito (cons b n1) r1 '() h))]
   [(fresh (n1 a r1)
           (conso 1 n1 n)
           (conso a r1 r)
           (== '(1) l)
           (splito n1 r1 '() h))]
   [(fresh (b n1 a r1 l1)
           (conso b n1 n)
           (conso a r1 r)
           (conso b l1 l)
           (poso l1)
           (splito n1 r1 l1 h))]))


(defrel (n-wider-than-mo x y q r)
  (fresh (xh xl qh ql yql yrql rr rh)
         (splito x r xl xh)
         (splito q r ql qh)
         (conde
          [(== '() xh)
           (== '() qh)
           (-o xl r yql)
           (*o y ql yql)]
          [(poso xh)
           (*o y ql yql)
           (+o r yql yrql)
           (-o yrql xl rr)
           (splito rr r '() rh)
           (/o xh y qh rh)])))


(defrel (logo n b q r)
  (conde
   [(== '() q) (<=o n b) (+o r '(1) n)]
   [(== '(1) q) (>1o b) (=lo n b) (+o r b n)]
   [(== '(1) b) (poso q) (+o r '(1) n)]
   [(== '() b) (poso q) (== r n)]
   [(== '(0 1) b)
    (fresh (a ad dd s)
           (poso dd)
           (== (cons a (cons ad dd)) n)
           (exp2o n '() q)
           (splito n dd r s))]
   [(<=o '(1 1) b)
    (<lo b n)
    (base-three-or-moreo n b q r)]))


(defrel (exp2o n b q)
  (conde
   [(== '(1) n) (== '() q)]
   [(>1o n)
    (== '(1) q)
    (fresh (s)
           (splito n b s '(1)))]
   [(fresh (q1 b2)
           (conso 0 q1 q)
           (poso q1)
           (<lo b n)
           (appendo b (cons 1 b) b2)
           (exp2o n b2 q1))]
   [(fresh (q1 nh b2 s)
           (conso 1 q1 q)
           (poso q1)
           (poso nh)
           (splito n b s nh)
           (appendo b (cons 1 b) b2)
           (exp2o nh b2 q1))]))


(defrel (base-three-or-moreo n b q r)
  (fresh (bw1 bw nw nw1 ql1 ql s)
         (exp2o b '() bw1)
         (+o bw1 '(1) bw)
         (<lo q n)
         (fresh (q1 bwq1)
                (+o q '(1) q1)
                (*o bw q1 bwq1)
                (<o nw1 bwq1))
         (exp2o n '() nw1)
         (+o nw1 '(1) nw)
         (/o nw bw ql s)
         (+o ql '(1) ql1)
         (<=lo ql q)
         (fresh (bql qh s qdh qd)
                (repeated-mulo b ql bql)
                (/o nw bw1 qh s)
                (+o ql qdh qh)
                (+o ql qd q)
                (<=o qd qdh)
                (<=o qd qdh)
                (fresh (bqd bq1 bq)
                       (repeated-mulo b qd bqd)
                       (*o bql bqd bq)
                       (*o b bq bq1)
                       (+o bq r n)
                       (<o n bq1)))))


(defrel (repeated-mulo n q nq)
  (conde
   [(poso n) (== '() q) (== '(1) nq)]
   [(== '(1) q) (== n nq)]
   [(>1o q)
    (fresh (q1 nq1)
           (+o q1 '(1) q)
           (repeated-mulo n q1 nq1)
           (*o nq1 n nq))]))