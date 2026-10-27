module

public import Certificates.Data.Kernel.SmithL6KT
public import Certificates.Data.SmithL6Pair

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6
open CFSG.SmithE (applyCols)

@[expose] def tvF (p : Nat × Nat) (φ : Nat) : Nat := if form φ p.1 then φ ^^^ p.2 else φ

@[expose] def wordV (w : List (Nat × Nat)) (x : Nat) : Nat := w.foldr tvA x

@[expose] def wordF (w : List (Nat × Nat)) (φ : Nat) : Nat := w.foldr tvF φ

@[expose] def wordId (w : List (Nat × Nat)) : Bool :=
  (List.range 6).all fun i => wordV w (2 ^ i) == 2 ^ i && wordF w (2 ^ i) == 2 ^ i

@[expose] def pairK (C k : Nat) : Nat × Nat := (fldW 12 C k / 64, fldW 12 C k % 64)

@[expose] def altW {α : Type} (p q : α) : Nat → List α
  | 0 => []
  | n + 1 => p :: q :: altW p q n

@[expose] def ord4K (C : Nat) : Bool :=
  (List.range 1953).all fun a => stabClsK C a == 6 || wordId (altW (pairK C 0) (pairK C a) 4)

@[expose] def stdK (C : Nat) : Bool :=
  pairK C 0 == (1, 2) && pairK C 31 == (2, 1) && (repsK C).getD 6 0 == 31 &&
    wordId (altW (pairK C 0) (pairK C 31) 3)

@[expose] def prUK (p : Nat × Nat) : Nat := ((List.range 64).find? fun u => form p.2 u).getD 0

@[expose] def prIdxK (W w : Nat) : Nat :=
  ((List.range 1395).find? fun i => fldW 20 W i == w).getD 1395

@[expose] def f3K (C I W : Nat) (T : List (List Nat)) : Bool :=
  (List.range 1953).all fun k =>
    !(tvImgP C I k 0 == 0 && tvImgP C I k 31 == 31) ||
      (let p := pairK C k
       let c := wedge3 1 2 (prUK p)
       let r := prIdxK W (wedge3 1 2 p.1)
       let w := fldW 20 W r
       decide (r < 1395) && applyCols (T.getD k []).toArray c ^^^ c == w &&
         applyCols (T.getD 0 []).toArray w == w && applyCols (T.getD 31 []).toArray w == w)

end CFSG.SmithL6.K
