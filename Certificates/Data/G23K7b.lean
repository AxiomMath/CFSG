module

public import Certificates.Data.G2ThreeMaxCheck

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbModule

open Certificates.G2ThreeMax

@[expose] def swapK7b (w : List ℕ) : List ℕ := w.map fun k => outerInput.sigma[k]!

@[expose] def invK7b (w : List ℕ) : List ℕ := w.reverse.map invK

@[expose] def k7bU : Fin 3 → List ℕ
  | 0 => [4, 0, 4, 7, 3, 7, 0, 3, 0, 3, 1]
  | 1 => [1, 5, 2, 0, 2, 0, 2, 4, 1, 6, 5, 6, 5, 2, 7, 3]
  | 2 => [7, 3, 7, 5, 3, 1, 2, 0, 3, 0, 3, 4, 0, 6, 5, 6, 5, 2, 7, 3]

@[expose] def k7bS : Fin 3 → List ℕ
  | 0 => [1, 4, 0, 4, 7, 3, 7, 3, 3, 1, 3, 1, 3]
  | 1 => [0, 2, 0, 2, 0, 2, 4, 6, 5, 6, 5, 7, 5]
  | 2 => [1, 4, 0, 2, 0, 2, 5, 7, 5, 7, 5, 6, 1, 3, 5]

@[expose] def k7bG0 : List ℕ := [4, 0, 4, 7, 3, 7, 1, 2, 1, 4, 6, 4, 6, 5, 2, 1, 7]

@[expose] def k7bSlp : Fin 4 → List ℕ
  | 0 => [3, 0, 5, 3, 4, 3, 0, 4, 0, 2, 4, 2, 4, 5, 0, 2, 3, 2, 4, 3]
  | 1 => [1, 4, 1, 0, 1, 0, 2, 0, 5, 0, 4, 3, 1]
  | 2 => [1, 4, 0, 5, 0, 4, 1, 3, 1, 0, 5, 2, 4, 0, 3, 0, 3, 2, 3, 2]
  | 3 => [3, 1, 3, 1, 4, 2, 0, 3, 0, 4, 1, 2, 4, 3, 0, 5, 3]

@[expose] def k7bRootLetter : Fin 4 → ℕ
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 6

@[expose] def kCArr (i : Fin 3) : Array ℕ :=
  mmul (wordArr k7bG0) (mmul (wordArr (k7bU i)) (wordArr (invK7b k7bG0)))

@[expose] def kHgArr (i : ℕ) : Array ℕ :=
  if i < 3 then wordArr (k7bU ⟨i % 3, Nat.mod_lt _ (by decide)⟩)
  else kCArr ⟨i % 3, Nat.mod_lt _ (by decide)⟩

@[expose] def kSlpArr (idxs : List ℕ) : Array ℕ :=
  idxs.foldr (fun i acc => mmul (kHgArr i) acc) idArr

@[expose] def kE8Arr : List (Array ℕ) :=
  let s1 := wordArr (k7bS 0)
  let s2 := wordArr (k7bS 1)
  let s3 := wordArr (k7bS 2)
  [idArr, s1, s2, s3, mmul s1 s2, mmul s1 s3, mmul s2 s3, mmul s1 (mmul s2 s3)]

@[expose] def nzFlat (a : Array ℕ) (p : ℕ) : Bool := a[p]! % 3 != 0

@[expose] def k7bCheck : Bool :=
  let s1 := wordArr (k7bS 0)
  let s2 := wordArr (k7bS 1)
  let s3 := wordArr (k7bS 2)
  (mmul (wordArr k7bG0) (wordArr (invK7b k7bG0)) == idArr) &&
    (mmul (wordArr (k7bU 0)) (wordArr (k7bU 0)) == idArr) &&
    (mmul (wordArr (k7bU 1)) (wordArr (k7bU 1)) == idArr) &&
    (mmul (wordArr (k7bU 2)) (wordArr (k7bU 2)) == idArr) &&
    (mmul s1 s1 == idArr) && (mmul s2 s2 == idArr) && (mmul s3 s3 == idArr) &&
    (wordArr (k7bU 0) == wordArr (swapK7b (k7bU 0))) &&
    (wordArr (k7bU 1) == wordArr (swapK7b (k7bU 1))) &&
    (wordArr (k7bU 2) == wordArr (swapK7b (k7bU 2))) &&
    (s1 == wordArr (swapK7b (k7bS 0))) && (s2 == wordArr (swapK7b (k7bS 1))) &&
    (s3 == wordArr (swapK7b (k7bS 2))) &&
    nzFlat (wordArr (k7bU 0)) 4 && nzFlat (wordArr (k7bU 1)) 4 && nzFlat (wordArr (k7bU 2)) 2 &&
    (mmul s1 s2 == mmul s2 s1) && (mmul s1 s3 == mmul s3 s1) && (mmul s2 s3 == mmul s3 s2) &&
    nzFlat s1 12 && nzFlat s2 2 && nzFlat s3 8 && nzFlat (mmul s1 s2) 2 &&
    nzFlat (mmul s1 s3) 8 && nzFlat (mmul s2 s3) 2 && nzFlat (mmul s1 (mmul s2 s3)) 2 &&
    kE8Arr.any (fun e => e == mmul (wordArr k7bG0) (mmul s1 (wordArr (invK7b k7bG0)))) &&
    kE8Arr.any (fun e => e == mmul (wordArr k7bG0) (mmul s2 (wordArr (invK7b k7bG0)))) &&
    kE8Arr.any (fun e => e == mmul (wordArr k7bG0) (mmul s3 (wordArr (invK7b k7bG0)))) &&
    (kSlpArr (k7bSlp 0) == genArr (k7bRootLetter 0)) &&
    (kSlpArr (k7bSlp 1) == genArr (k7bRootLetter 1)) &&
    (kSlpArr (k7bSlp 2) == genArr (k7bRootLetter 2)) &&
    (kSlpArr (k7bSlp 3) == genArr (k7bRootLetter 3))

end CFSG.CGT.PushingUpLit.CGT6.EmbModule
