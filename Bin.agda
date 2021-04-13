{-# OPTIONS --no-unicode #-}

module Homework.Bin where

import Lib.Nat as Nat
open Nat using (Nat; _+N_)
open import Lib.Eq
open import Lib.Sigma
open import Lib.Zero
open import Lib.One

data Bin : Set where
  end : Bin
  _O : Bin -> Bin
  _I : Bin -> Bin

infixr 12 _O
infixr 12 _I

_ : Bin
_ = end I O I

suc : Bin -> Bin
suc end = end I
suc (x O) = x I
suc (x I) = (suc x) O

_ : suc end == end I
_ = refl

_ : suc (end I I) == end I O O
_ = refl

toNat : Bin -> Nat
toNat end = 0
toNat (x O) = (toNat x) +N (toNat x)
toNat (x I) = Nat.suc((toNat x) +N (toNat x))

_ : toNat (end I I I) == 7
_ = refl

_ : toNat (end I I O) == 6
_ = refl

_ : toNat (end O) == 0
_ = refl

_ : toNat end == 0
_ = refl

fromNat : Nat -> Bin
fromNat Nat.zero = end
fromNat (Nat.suc x) = suc (fromNat x)

_ : fromNat 0 == end
_ = refl

_ : fromNat 1 == end I
_ = refl

_ : fromNat 8 == end I O O O
_ = refl

toNat-suc : (b : Bin) -> toNat (suc b) == Nat.suc (toNat b)
toNat-suc end = refl
toNat-suc (b O) = ap Nat.suc refl
toNat-suc (b I) rewrite toNat-suc b = ap Nat.suc (Nat.+N-right-suc (toNat b) (toNat b))

to-from-id : (n : Nat) -> toNat (fromNat n) == n
to-from-id Nat.zero = refl
to-from-id (Nat.suc n) rewrite to-from-id n =
  (toNat (suc (fromNat n)))
    =[ toNat-suc (fromNat n) >=
  Nat.suc (toNat (fromNat n))
    =[ ap Nat.suc (to-from-id n) >=
  Nat.suc n
    QED

data LeadingOne : Bin -> Set where
  endI : LeadingOne (end I)
  _O : {b : Bin} -> LeadingOne b -> LeadingOne (b O)
  _I : {b : Bin} -> LeadingOne b -> LeadingOne (b I)

data Can : Bin -> Set where
  end : Can end
  leadingOne : {b : Bin} -> LeadingOne b -> Can b

suc-LeadingOne : (b : Bin) -> LeadingOne b -> LeadingOne (suc b)
suc-LeadingOne .(end I) endI = endI O
suc-LeadingOne (b O) (x O) = x I
suc-LeadingOne (b I) (x I) = suc-LeadingOne b x O

suc-Can : (b : Bin) -> Can b -> Can (suc b)
suc-Can .end end = leadingOne endI
suc-Can b (leadingOne x) = leadingOne (suc-LeadingOne b x)

fromNat-Can : (n : Nat) -> Can (fromNat n)
fromNat-Can Nat.zero = end
fromNat-Can (Nat.suc n) = suc-Can (fromNat n) (fromNat-Can n)

_+B_ : Bin -> Bin -> Bin
end +B y = y
x O +B end = x O
x O +B y O = (x +B y) O
x O +B y I = (x +B y) I
x I +B end = x I
x I +B y O = (x +B y) I
x I +B y I = (suc (x +B y)) O

infixr 11 _+B_

_ : end +B end I I I I == end I I I I
_ = refl

_ : end I O O +B end == end I O O
_ = refl

_ : end I I +B end I I I I == end I O O I O
_ = refl

_ : end I I I +B end I O I == end I I O O
_ = refl

+B-right-end : (b : Bin) -> b +B end == b
+B-right-end end = refl
+B-right-end (b O) = refl
+B-right-end (b I) = refl

+B-left-suc : (b v : Bin) -> suc b +B v == suc (b +B v)
+B-left-suc end end = refl
+B-left-suc (b O) end = refl
+B-left-suc (b I) end = refl
+B-left-suc end (v O) = refl
+B-left-suc (b O) (v O) = refl
+B-left-suc (b I) (v O) = ap _O (+B-left-suc b v)
+B-left-suc end (v I) = refl
+B-left-suc (b O) (v I) = refl
+B-left-suc (b I) (v I) = ap _I (+B-left-suc b v)

+B-right-suc : (b v : Bin) -> b +B suc v == suc (b +B v)
+B-right-suc end v = refl
+B-right-suc (b O) end rewrite +B-right-end b = refl
+B-right-suc (b O) (v O) = refl
+B-right-suc (b O) (v I) rewrite +B-right-suc b v = refl
+B-right-suc (b I) end rewrite +B-right-end b = refl
+B-right-suc (b I) (v O) = refl
+B-right-suc (b I) (v I) rewrite +B-right-suc b v = refl

fromNat-assoc : (n m : Nat) -> fromNat (n +N m) == fromNat n +B fromNat m
fromNat-assoc Nat.zero m = refl
fromNat-assoc (Nat.suc n) m rewrite fromNat-assoc n m = ==-symm (+B-left-suc (fromNat n) (fromNat m))

fromNat-+N-+B-commutes : (n m : Nat) -> fromNat (n +N m) == fromNat n +B fromNat m
fromNat-+N-+B-commutes Nat.zero m = refl
fromNat-+N-+B-commutes (Nat.suc n) m =
  suc (fromNat (n +N m))
    =[ ap suc (fromNat-assoc n m) >=
  suc (fromNat n +B fromNat m)
    =[ ==-symm (+B-left-suc (fromNat n) (fromNat m)) >=
  suc (fromNat n) +B fromNat m
    QED

+B-same-shift : (b : Bin) -> LeadingOne b -> b +B b == b O
+B-same-shift .(end I) endI = refl
+B-same-shift .(_ O) (x O) = ap _O (+B-same-shift _ x)
+B-same-shift (b I) (x I) rewrite +B-same-shift b x = ap _O refl

from-to-id : (b : Bin) -> LeadingOne b -> fromNat (toNat b) == b
from-to-id .(end I) endI = refl
from-to-id (b O) (x O) rewrite
  fromNat-assoc (toNat b) (toNat b) |
  from-to-id b x = +B-same-shift b x
from-to-id (b I) (x I) rewrite
  fromNat-assoc (toNat b) (toNat b) |
  from-to-id b x |
  +B-same-shift b x = refl

from-to-id-Can : (b : Bin) -> Can b -> fromNat (toNat b) == b
from-to-id-Can .end end = refl
from-to-id-Can b (leadingOne x) = from-to-id b x
