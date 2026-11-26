;;  THE ROOTS OF LISP
;;
;; https://languagelog.ldc.upenn.edu/myl/llog/jmc.pdf

(ns the_roots_of_lisp
  (:refer-clojure :exclude [and assoc atom eval cond]))


;;  0. SETUP
;;
;; Clojure doesn't have an equivalent for some primitives the original
;; text uses. Here we adapt it little to serve our purpose. The reader
;; may skip this section or come back later for curiosity.
;; 
;; NOTE: In this implementation we will use `nil` instead `'()` to
;; represent falsity since it's already handled by Clojure as such.

(defn atom [x]
  (clojure.core/cond
    (not (clojure.core/and (seq? x)
                           (seq x))) 't
    :else                            nil))

(defn eq [x y]
  (clojure.core/cond
    (clojure.core/and (atom x)
                      (atom y)
                      (= x y)) 't
    :else                      nil))

(def car first)

(def cdr rest)

(defmacro cond [& body]
  `(clojure.core/cond ~@(mapcat identity body)))


;;  1. SEVEN PRIMITIVE OPERATORS
;;

;; 1. quote:
;;
;; Differentiate code from plain data. Applied to an atom it retuns
;; the atom itself instead of it's value. When applied to a list it
;; returns the plain list instead of executing it as code. Examples:
(quote a)
'a
'(a b c)

;; 2. atom
;;
;; Sequence of characters that represents the smallest unit of element
;; we can have. Examples:
(atom 'a)
(atom '())
(atom '(a b c))

;; 3. eq
;;
;; Checks the equality of two atoms, not lists. Examples:
(eq 'a 'a)
(eq 'a 'b)
(eq '() '())
(eq nil nil)
(eq '(a b) '(a b))

;; 4. car
;;
;; Extract the first element of a list. Example:
(car '(a b c))

;; 5. cdr
;;
;; Returns the remaining of the list without the first
;; element. Example:
(cdr '(a b c))

;; 6. cons
;;
;; Given an element `x` and a list `y`, puts `x` in the head of
;; `y`. Example:
(cons 'a '(b c))

;; 7. cond
;;
;; In the form (cond (p1 e1) ...(pn en)) - The `p` expressions are
;; evaluated until one of them is true, in this case the corresponding
;; `e` expression is evaluated. Example:
(cond ((eq 'a 'b) 'first)
      ((atom 'a)  'second))


;;  2. DENOTATING FUNCTIONS

;; We can denotate and call a function in the following
;; form: ((lambda (p1 ...pn) e) a1 ...an). Examples:
((fn [x]   (cons x '(b c))) 'a)
((fn [x y] (cons x (cdr y))) 'z '(a b c))

;; Functions can be used as operators and parameters to other
;; functions:
((fn [f] (f '(b c)))
 (fn [x] (cons 'a x)))

;; Functions can be called recursevely if we define a name for it:
(defn subs [x y z]
  (cond ((atom z)
         (cond ((eq y z) x)
               ('t z)))
        ('t (cons (subs x y (car z))
                  (subs x y (cdr z))))))

(subs 'm 'b '(a b (a b c) d))


;;  3. SOME FUNCTIONS

;; Abbreviations
(defn caar   [x] (car (car x)))
(defn cadr   [x] (car (cdr x)))
(defn cdar   [x] (cdr (car x)))
(defn caddr  [x] (car (cdr (cdr x))))
(defn cadar  [x] (car (cdr (car x))))
(defn caddar [x] (car (cdr (cdr (car x)))))

(caar  '((a b) (c d) e))
(cadr  '((a b) (c d) e))
(cdar  '((a b) (c d) e))
(caddr '((a b) (c d) e))
(cadar '((a b) (c d) e))
(caddar '((a b c) (c d) e))

(list 'a 'b 'c)

;; Helpers
(defn null [x]
  (eq x '()))

(null 'a)
(null '())

(defn and [x y]
  (cond (x (cond (y 't) ('t nil)))
        ('t nil)))

(and (atom 'a) (eq 'a 'a))

(defn not [x]
  (cond (x nil) ('t 't)))

(not (eq 'a 'a))
(not (eq 'a 'b))

(defn append [x y]
  (cond ((null x) y)
        ('t (cons (car x) (append (cdr x) y)))))

(append '(a b) '(c d))
(append '() '(c d))

(defn pair [x y]
  (cond ((null x) '())
        ((null y) '())
        ('t (cons (list (car x) (car y))
                  (pair (cdr x) (cdr y))))))

(pair '(a b c) '(x y z))
(pair '(a b c) '())
(pair '() '(x y z))

(defn assoc [x y]
  (cond ((null? y) nil)
        ((eq x (caar y)) (cadar y))
        ('t (assoc* x (cdr y)))))

(assoc 'x '((x a) (y b)))
(assoc 'x '((x a') (x a) (y b)))
(assoc 'z '((x a) (y b)))


;;  4. THE SURPRISE
(declare evcon)
(declare evlis)

(defn eval [e a]
  (cond
    ((atom e) (assoc e a))
    ((atom (car e))
     (cond
       ((eq (car e) 'quote) (cadr e))
       ((eq (car e) 'atom)  (atom (eval (cadr e) a)))
       ((eq (car e) 'eq)    (eq   (eval (cadr e) a)
                                  (eval (caddr e) a)))
       ((eq (car e) 'car)   (car  (eval (cadr e) a)))
       ((eq (car e) 'cdr)   (cdr  (eval (cadr e) a)))
       ((eq (car e) 'cons)  (cons (eval (cadr e) a)
                                  (eval (caddr e) a)))
       ((eq (car e) 'cond)  (evcon (cdr e) a))                                  
       ('t (eval (cons (assoc (car e) a)
                       (cdr e))
                 a))))
    ((eq (caar e) 'label)
     (eval (cons (caddar e) (cdr e))
           (cons (list (cadar e) (car e)) a)))
    ((eq (caar e) 'lambda)
     (eval (caddar e)
           (append (pair (cadar e) (evlis (cdr e) a))
                   a)))))

(defn evcon [c a]
  (cond ((eval (c
                aar c) a)
         (eval (cadar c) a))
        ('t (evcon (cdr c) a))))

(defn evlis [m a]
  (cond ((null m) '())
         ('t (cons (eval (car m) a)
                   (evlis (cdr m) a)))))

(eval 'x '((x a) (y b)))

(eval '(quote x) '())

(eval '(atom '()) '())

(eval '(eq 'a 'a) '())

(eval '(car '(a b c)) '())

(eval '(cdr '(a b c)) '())

(eval '(cons x '(b c)) '((x a) (y b)))

(eval '(cond ((atom x) 'atom)
             ('t 'list)) '((x '(a b))))

(eval '(f '(b c))
      '((f (lambda (x) (cons 'a x)))))

(eval '((lambda (x y) (cons x (cdr y)))
        'a
        '(z b c))
      '())

(eval '((label firstatom (lambda (x)
                                 (cond ((atom x) x)
                                       ('t (firstatom (car x))))))
        y)
      '((y ((a b) (c d)))))
