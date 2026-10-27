module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Check
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Std.Data.HashMap

public section

namespace CFSG.KC.EvenSporCocode

open CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

@[expose] def encT (t : List ℕ) : ℕ := t.foldr (fun x acc => x + acc * 32) 0

@[expose] def encAll (L : List (List ℕ)) : ℕ := L.foldr (fun t acc => encT t + (acc <<< 120)) 0

@[expose] def dig (X i : ℕ) : ℕ := (X >>> (5 * i)) % 32

@[expose] def tmulK (S T : ℕ) : ℕ := encT ((List.range 24).map fun i => dig S (dig T i))

@[expose] def fldE (EP k : ℕ) : ℕ := (EP >>> (120 * k)) % 2 ^ 120

@[expose] def lookK (RB : List ℕ) (i j : ℕ) : ℕ :=
  if j < 1024 then (RB.getD (i / 32) 0 >>> (10 * (1024 * (i % 32) + j))) % 1024 else 0

@[expose] def zeroSeg (RB : List ℕ) (i : ℕ) : Bool :=
  (RB.getD (i / 32) 0 >>> (10240 * (i % 32))) % 2 ^ 10240 == 0

@[expose] def colsK (L : List (List ℕ)) (i : ℕ) : List ℕ := colsOfTab (L.getD i [])

@[expose] def rowGo (EP : ℕ) (RB : List ℕ) (i T : ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | U :: Us, j => tmulK T U == fldE EP (lookK RB i j) && rowGo EP RB i T Us (j + 1)

@[expose] def rowsAt (EP : ℕ) (RB : List ℕ) (L : List (List ℕ)) (K : List ℕ) (i : ℕ) : Bool :=
  if isInv (L.getD i []) then rowGo EP RB i (K.getD i 0) K 0 else zeroSeg RB i

@[expose] def rowsBlk (EP : ℕ) (RB : List ℕ) (L : List (List ℕ)) (K : List ℕ) (b : ℕ) : Bool :=
  (List.range' (32 * b) 32).all (rowsAt EP RB L K)

@[expose] def fldC (CB p : ℕ) : ℕ := (CB >>> (10 * p)) % 1024

@[expose] def closeRow (EP CB : ℕ) (l : List ℕ) (i : ℕ) : List (List ℕ) → ℕ → Bool
  | [], _ => true
  | g :: gs, m => encT (tmul l g) == fldE EP (fldC CB (10 * i + m)) && closeRow EP CB l i gs (m + 1)

@[expose] def closeGo (EP CB : ℕ) (gs : List (List ℕ)) : List (List ℕ) → ℕ → Bool
  | [], _ => true
  | l :: ls, i => closeRow EP CB l i gs 0 && closeGo EP CB gs ls (i + 1)

@[expose] def validB (t : List ℕ) : Bool := t.length == 24 && t.all (· < 24)

@[expose] def childrenSub (mulIdx : ℕ → ℕ → ℕ) (cols : ℕ → List ℕ)
    (d : List ℕ → List ℕ → List ℕ → Bool) (V F cand sub : List ℕ) : Bool :=
  sub.all fun c =>
    !validExt mulIdx V c || d (extV mulIdx V c) (extF cols F c) (extC mulIdx cand c)

@[expose] def invsK (L : List (List ℕ)) : List ℕ :=
  (List.range 1024).filter fun i => isInv (L.getD i [])

@[expose] def dfsSub (RB : List ℕ) (L : List (List ℕ)) (cands sub : List ℕ) : Bool :=
  childrenSub (lookK RB) (colsK L) (dfs (lookK RB) (colsK L) 9) [0] (List.range 4096) cands sub

@[expose] def planeK (j : ℕ) : ℕ :=
  Nat.mul (Nat.div (Nat.sub (Nat.shiftLeft 1 4096) 1)
      (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 (Nat.succ j))) 1))
    (Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 j)) 1) (Nat.shiftLeft 1 j))

@[expose] def planesB : Bool :=
  (List.range 12).all fun j => (List.range 4096).all fun m =>
    Nat.beq (Nat.land (Nat.shiftRight (planeK j) m) 1) (Nat.land (Nat.shiftRight m j) 1)

@[expose] def imgPl (k : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | j, c :: cs => (bif c.testBit k then planeK j else 0) ^^^ imgPl k (j + 1) cs

@[expose] def movedK (cs : List ℕ) : ℕ :=
  (List.range 12).foldr (fun k acc => (imgPl k 0 cs ^^^ planeK k) ||| acc) 0

@[expose] def strictL (y : ℕ) (k : ℕ → List ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] def extFK (cols : ℕ → List ℕ) (F : List ℕ) (c : ℕ) : List ℕ :=
  strictL (movedK (cols c)) fun D => F.filter fun m => Nat.beq (Nat.land (Nat.shiftRight D m) 1) 0

@[expose] def childrenK (mulIdx : ℕ → ℕ → ℕ) (cols : ℕ → List ℕ)
    (d : List ℕ → List ℕ → List ℕ → Bool) (V F cand : List ℕ) : Bool :=
  cand.all fun c =>
    !validExt mulIdx V c || d (extV mulIdx V c) (extFK cols F c) (extC mulIdx cand c)

@[expose] def dfsK (mulIdx : ℕ → ℕ → ℕ) (cols : ℕ → List ℕ) : ℕ → List ℕ → List ℕ → List ℕ → Bool
  | 0, V, F, _ => decide (V.length * F.length ≤ 2 ^ 11)
  | n + 1, V, F, cand =>
      decide (V.length * F.length ≤ 2 ^ 11) && childrenK mulIdx cols (dfsK mulIdx cols n) V F cand

@[expose] def childrenSubK (mulIdx : ℕ → ℕ → ℕ) (cols : ℕ → List ℕ)
    (d : List ℕ → List ℕ → List ℕ → Bool) (V F cand sub : List ℕ) : Bool :=
  sub.all fun c =>
    !validExt mulIdx V c || d (extV mulIdx V c) (extFK cols F c) (extC mulIdx cand c)

@[expose] def dfsSubK (RB : List ℕ) (L : List (List ℕ)) (cands sub : List ℕ) : Bool :=
  childrenSubK (lookK RB) (colsK L) (dfsK (lookK RB) (colsK L) 9) [0] (List.range 4096) cands sub

end CFSG.KC.EvenSporCocode
