module

public import Certificates.Data.T84P

public section

namespace Certificates.T84S4

open Certificates.T84P
open Certificates.A5GL42 (ofCode vecOfCode)

@[expose] def tCodes : Array ℕ :=
  #[33825, 8580, 32475, 56190, 5097, 12909, 19638, 27954, 38856, 46668, 51351, 59667]

@[expose] def elt (i : ℕ) : Elt := (vecOfCode (i / 12), ofCode (tCodes.getD (i % 12) 0))

@[expose] def Ml (_ : Unit := ()) : List Elt := (List.range 192).map elt

def actArr : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14,
   3, 7, 11, 15, 0, 11, 13, 6, 14, 5, 3, 8, 7, 12, 10, 1, 9, 2, 4, 15, 0, 14, 7, 9, 11, 5, 12, 2,
   13, 3, 10, 4, 6, 8, 1, 15, 0, 13, 6, 11, 2, 15, 4, 9, 3, 14, 5, 8, 1, 12, 7, 10, 0, 9, 14, 7, 3,
   10, 13, 4, 1, 8, 15, 6, 2, 11, 12, 5, 0, 2, 3, 1, 13, 15, 14, 12, 6, 4, 5, 7, 11, 9, 8, 10, 0,
   6, 11, 13, 12, 10, 7, 1, 4, 2, 15, 9, 8, 14, 3, 5, 0, 12, 4, 8, 6, 10, 2, 14, 11, 7, 15, 3, 13,
   1, 9, 5, 0, 8, 12, 4, 7, 15, 11, 3, 9, 1, 5, 13, 14, 6, 2, 10, 0, 3, 1, 2, 9, 10, 8, 11, 14, 13,
   15, 12, 7, 4, 6, 5, 0, 7, 9, 14, 8, 15, 1, 6, 12, 11, 5, 2, 4, 3, 13, 10]

def tmulArr : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 1, 0, 3, 2, 11, 7, 9, 5, 10, 6, 8, 4, 2, 3, 0, 1, 6, 8,
   4, 10, 5, 11, 7, 9, 3, 2, 1, 0, 9, 10, 11, 8, 7, 4, 5, 6, 4, 6, 9, 11, 8, 3, 7, 1, 0, 10, 2, 5,
   5, 10, 7, 8, 2, 9, 3, 4, 6, 0, 11, 1, 6, 4, 11, 9, 5, 1, 10, 3, 2, 7, 0, 8, 7, 8, 5, 10, 3, 6,
   2, 11, 9, 1, 4, 0, 8, 7, 10, 5, 0, 11, 1, 6, 4, 2, 9, 3, 9, 11, 4, 6, 7, 0, 8, 2, 3, 5, 1, 10,
   10, 5, 8, 7, 1, 4, 0, 9, 11, 3, 6, 2, 11, 9, 6, 4, 10, 2, 5, 0, 1, 8, 3, 7]

def invArr : Array ℕ :=
  #[0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 12, 49, 134, 171, 152, 105, 46, 95, 160, 113, 30, 79, 24,
   97, 158, 87, 56, 153, 22, 119, 76, 173, 42, 139, 36, 145, 74, 111, 104, 57, 34, 179, 136, 89,
   18, 163, 48, 13, 170, 135, 80, 93, 118, 107, 28, 41, 162, 151, 60, 61, 62, 63, 128, 189, 130,
   191, 184, 125, 186, 127, 72, 109, 38, 147, 32, 141, 106, 23, 52, 161, 174, 91, 84, 157, 98, 27,
   176, 45, 142, 83, 112, 53, 150, 19, 96, 25, 86, 159, 140, 117, 178, 155, 40, 17, 78, 55, 108,
   73, 146, 39, 92, 21, 166, 143, 172, 101, 54, 31, 120, 121, 122, 123, 188, 69, 190, 71, 64, 185,
   66, 187, 132, 169, 14, 51, 44, 165, 154, 35, 100, 77, 90, 115, 144, 37, 110, 75, 164, 177, 94,
   59, 16, 29, 138, 103, 156, 85, 26, 99, 20, 81, 58, 47, 148, 137, 114, 175, 168, 133, 50, 15,
   116, 33, 82, 167, 88, 149, 102, 43, 180, 181, 182, 183, 68, 129, 70, 131, 124, 65, 126, 67]

def mulFlat (_ : Unit := ()) : Array ℕ :=
  Array.ofFn (n := 192 * 192) fun p =>
    ((p.val / 192 / 12) ^^^ actArr.getD (16 * (p.val / 192 % 12) + p.val % 192 / 12) 0) * 12 +
      tmulArr.getD (12 * (p.val / 192 % 12) + p.val % 192 % 12) 0

@[expose] def tb (fl : Array ℕ) (i j : ℕ) : ℕ := fl.getD (192 * i + j) 0

@[expose] def mulT (i j : ℕ) : ℕ := tb (mulFlat ()) i j

@[expose] def invT (i : ℕ) : ℕ := invArr.getD i 0

@[expose] def jT (i : ℕ) : Bool := decide (i % 12 < 4)

@[expose] def jgIdx : List ℕ := [50, 181, 158, 110]

@[expose] def pow44 (z : Elt) : Elt :=
  let z2 := mulE z z
  let z4 := mulE z2 z2
  let z8 := mulE z4 z4
  let z16 := mulE z8 z8
  let z32 := mulE z16 z16
  mulE z32 (mulE z8 z4)

@[expose] def gy : ℕ := 191

structure Facts : Prop where
  one : elt 0 = oneE
  mem : ∀ i < 192, elt i ∈ M0l
  inj : ∀ i < 192, ∀ j < 192, elt i = elt j → i = j
  tab : ∀ i < 192, ∀ j < 192, mulT i j < 192 ∧ mulE (elt i) (elt j) = elt (mulT i j)
  inv : ∀ i < 192, invT i < 192 ∧ mulT i (invT i) = 0
  jT_iff : ∀ i < 192, jT i = true ↔ elt i ∈ Jl
  jl_sub : ∀ x ∈ Jl, x ∈ Ml ()
  norm : ∀ i < 192, ∀ j < 192, jT j = true → jT (mulT (mulT i j) (invT i)) = true
  gen3 : gy < 192 ∧ mulT (mulT gy gy) gy = 0 ∧
    ∀ i < 192, mulT (mulT i i) i = 0 ∨ mulT (mulT (mulT i gy) (mulT i gy)) (mulT i gy) = 0
  fpf : ∀ i < 192, i ≠ 0 → mulT (mulT i i) i = 0 → ∀ j < 192, jT j = true →
    mulT i j = mulT j i → j = 0
  jg : ∀ i ∈ jgIdx, i < 192 ∧ elt i ∈ Jl
  odd : ∀ z ∈ M0l, mulE z (pow44 z) = oneE →
    (∀ i ∈ jgIdx, mulE (mulE z (elt i)) (pow44 z) ∈ Jl) → z ∈ Ml ()
  autFix : ∀ f : ℕ → ℕ, (∀ i < 192, f i < 192) → f 0 = 0 →
    (∀ i < 192, ∀ j < 192, f (mulT i j) = mulT (f i) (f j)) → (∀ i < 192, f (f i) = i) →
    ((List.range 192).filter fun x => jT x && f x == x).length = 4 →
    (∀ i < 192, jT i = true → f i = i → mulT i i = 0) →
      ∃ y < 192, y ≠ 0 ∧ mulT (mulT y y) y = 0 ∧ f y = y

end Certificates.T84S4
