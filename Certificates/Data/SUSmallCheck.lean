module

public import Certificates.Data.SUSmallBase
public import Mathlib.Data.List.GetD
public import Mathlib.Data.ZMod.Basic

public section

namespace Certificates.SUSmall

open CFSG.StandardType.HdRo7SU.Small

abbrev Vec (m : ℕ) : Type := Fin m → ZMod 3

abbrev Pair (m : ℕ) : Type := Vec m × Vec m

@[expose] def pairCode (x y : ZMod 3) : Fin 9 :=
  ⟨x.val * 3 + y.val, by have hx := ZMod.val_lt x; have hy := ZMod.val_lt y; omega⟩

instance {m : ℕ} (p : Pair m) : Decidable (SMTClass p) := by unfold SMTClass; infer_instance

instance {m : ℕ} (p q : Pair m) : Decidable (SMClass p q) := by unfold SMClass; infer_instance

@[expose] def uOf (k : Fin 9) : ZMod 3 := ((k.val / 3 : ℕ) : ZMod 3)

@[expose] def phiOf (k : Fin 9) : ZMod 3 := ((k.val % 3 : ℕ) : ZMod 3)

@[expose] def negCode (k : Fin 9) : Fin 9 := pairCode (-(uOf k)) (-(phiOf k))

@[expose] def key {m : ℕ} (p : Pair m) : List ℕ :=
  (List.finRange 9).map fun k =>
    (Finset.univ.filter (fun i : Fin m => pairCode (p.1 i) (p.2 i) = k)).card

@[expose] def negKey (c : List ℕ) : List ℕ :=
  (List.finRange 9).map fun k => c.getD (negCode k) 0

@[expose] def enc (c : List ℕ) : ℕ :=
  (List.finRange 9).foldl (fun acc k => acc * 10 + c.getD k 0) 0

@[expose] def ckey {m : ℕ} (p : Pair m) : List ℕ :=
  if enc (key p) ≤ enc (negKey (key p)) then key p else negKey (key p)

@[expose] def ckeyOfList (c : List ℕ) : List ℕ :=
  if enc c ≤ enc (negKey c) then c else negKey c

@[expose] def dotCount (c : List ℕ) : ZMod 3 :=
  ∑ k : Fin 9, ((c.getD k 0 : ℕ) : ZMod 3) * (uOf k * phiOf k)

@[expose] def zCount (c : List ℕ) : Bool :=
  (List.finRange 9).all fun k => (List.finRange 9).all fun l =>
    (c.getD k 0 == 0) || (c.getD l 0 == 0) ||
      ((uOf k == uOf l) == (phiOf k == phiOf l))

@[expose] def validCount (c : List ℕ) : Bool := zCount c && (dotCount c == 2)

@[expose] def countOne {m : ℕ} (a : Vec m) : ℕ := (List.finRange m).countP fun i => a i == 1

@[expose] def countTwo {m : ℕ} (a : Vec m) : ℕ := (List.finRange m).countP fun i => a i == 2

@[expose] def isTranspositionPair {m : ℕ} (p : Pair m) : Bool :=
  (p.1 == p.2) && (countOne p.1 == 1) && (countTwo p.1 == 1)

@[expose] def zeroPairZ {m : ℕ} (p : Pair m) : Bool :=
  (List.finRange m).all fun i => (List.finRange m).all fun j =>
    ((p.1 i == p.1 j) == (p.2 i == p.2 j))

@[expose] def sameLine {m : ℕ} (a b : Vec m) : Bool :=
  (a == b) || (a == fun i => (-1 : ZMod 3) * b i)

@[expose] def conj {m : ℕ} (r s : Pair m) : Pair m :=
  (s.1 - smDot r.2 s.1 • r.1, s.2 - smDot s.2 r.1 • r.2)

@[expose] def repeatedLine {m : ℕ} (r s : Pair m) : Bool :=
  (r != s) && (r != (fun i => -(s.1 i), fun i => -(s.2 i))) &&
    (sameLine r.1 s.1 || sameLine r.2 s.2)

@[expose] def fixesAxis {m : ℕ} (p : Pair m) : Bool :=
  ((∑ i, p.2 i) == 0) && !isTranspositionPair p

@[expose] def badPair {m : ℕ} (r s : Pair m) : Bool :=
  let c := conj r s
  repeatedLine r s ||
    ((smDot r.2 s.1 == 0) != (smDot s.2 r.1 == 0)) ||
    !zeroPairZ c || fixesAxis c

@[expose] def cat7 : List (Pair 7) :=   [
    (![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 2]),
    (![0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 1, 1]),
    (![0, 0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 0, 1, 2]),
    (![0, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 2, 2, 2, 2]),
    (![0, 0, 0, 1, 1, 1, 2], ![0, 0, 0, 2, 2, 2, 1]),
    (![0, 0, 0, 1, 1, 2, 2], ![0, 0, 0, 2, 2, 1, 1]),
    (![0, 0, 1, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1, 1]),
    (![0, 0, 1, 1, 1, 1, 2], ![0, 0, 1, 1, 1, 1, 2]),
    (![0, 0, 1, 1, 1, 2, 2], ![0, 0, 1, 1, 1, 2, 2]),
    (![0, 0, 0, 0, 0, 0, 1], ![1, 1, 1, 1, 1, 1, 2]),
    (![0, 0, 0, 0, 0, 1, 2], ![1, 1, 1, 1, 1, 2, 0]),
    (![0, 0, 0, 0, 0, 2, 2], ![1, 1, 1, 1, 1, 2, 2]),
    (![0, 0, 0, 0, 1, 2, 2], ![1, 1, 1, 1, 0, 2, 2]),
    (![0, 0, 0, 0, 1, 2, 2], ![1, 1, 1, 1, 2, 0, 0]),
    (![0, 0, 0, 1, 1, 2, 2], ![1, 1, 1, 0, 0, 2, 2]),
    (![0, 0, 0, 1, 1, 1, 1], ![1, 1, 1, 2, 2, 2, 2]),
    (![0, 0, 0, 1, 2, 2, 2], ![1, 1, 1, 2, 0, 0, 0]),
    (![0, 0, 1, 1, 1, 2, 2], ![1, 1, 0, 0, 0, 2, 2]),
    (![0, 0, 1, 1, 1, 1, 2], ![1, 1, 2, 2, 2, 2, 0]),
    (![0, 0, 1, 2, 2, 2, 2], ![1, 1, 2, 0, 0, 0, 0]),
    (![0, 0, 2, 2, 2, 2, 2], ![1, 1, 2, 2, 2, 2, 2]),
    (![0, 1, 1, 1, 1, 2, 2], ![1, 0, 0, 0, 0, 2, 2]),
    (![0, 1, 2, 2, 2, 2, 2], ![1, 0, 2, 2, 2, 2, 2]),
    (![0, 1, 1, 1, 1, 2, 2], ![1, 2, 2, 2, 2, 0, 0]),
    (![0, 1, 2, 2, 2, 2, 2], ![1, 2, 0, 0, 0, 0, 0]),
    (![1, 1, 1, 1, 1, 1, 2], ![0, 0, 0, 0, 0, 0, 1]),
    (![1, 1, 1, 1, 1, 2, 2], ![0, 0, 0, 0, 0, 2, 2]),
    (![1, 1, 1, 2, 2, 2, 2], ![0, 0, 0, 1, 1, 1, 1]),
    (![1, 1, 2, 2, 2, 2, 2], ![0, 0, 2, 2, 2, 2, 2]),
    (![1, 1, 1, 1, 1, 1, 1], ![2, 2, 2, 2, 2, 2, 2]),
    (![1, 1, 1, 1, 1, 1, 2], ![2, 2, 2, 2, 2, 2, 1]),
    (![1, 1, 1, 1, 1, 2, 2], ![2, 2, 2, 2, 2, 1, 1]),
    (![1, 1, 1, 1, 2, 2, 2], ![2, 2, 2, 2, 1, 1, 1])
  ]

@[expose] def cat8 : List (Pair 8) :=   [
    (![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 2]),
    (![0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 1]),
    (![0, 0, 0, 0, 0, 0, 1, 2], ![0, 0, 0, 0, 0, 0, 1, 2]),
    (![0, 0, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 2, 2, 2, 2]),
    (![0, 0, 0, 0, 1, 1, 1, 2], ![0, 0, 0, 0, 2, 2, 2, 1]),
    (![0, 0, 0, 0, 1, 1, 2, 2], ![0, 0, 0, 0, 2, 2, 1, 1]),
    (![0, 0, 0, 1, 1, 1, 1, 1], ![0, 0, 0, 1, 1, 1, 1, 1]),
    (![0, 0, 0, 1, 1, 1, 1, 2], ![0, 0, 0, 1, 1, 1, 1, 2]),
    (![0, 0, 0, 1, 1, 1, 2, 2], ![0, 0, 0, 1, 1, 1, 2, 2]),
    (![0, 1, 1, 1, 1, 1, 1, 1], ![0, 2, 2, 2, 2, 2, 2, 2]),
    (![0, 1, 1, 1, 1, 1, 1, 2], ![0, 2, 2, 2, 2, 2, 2, 1]),
    (![0, 1, 1, 1, 1, 1, 2, 2], ![0, 2, 2, 2, 2, 2, 1, 1]),
    (![0, 1, 1, 1, 1, 2, 2, 2], ![0, 2, 2, 2, 2, 1, 1, 1]),
    (![0, 0, 0, 0, 0, 0, 0, 1], ![1, 1, 1, 1, 1, 1, 1, 2]),
    (![0, 0, 0, 0, 0, 0, 1, 2], ![1, 1, 1, 1, 1, 1, 2, 0]),
    (![0, 0, 0, 0, 0, 0, 2, 2], ![1, 1, 1, 1, 1, 1, 2, 2]),
    (![0, 0, 0, 0, 0, 1, 2, 2], ![1, 1, 1, 1, 1, 0, 2, 2]),
    (![0, 0, 0, 0, 0, 1, 2, 2], ![1, 1, 1, 1, 1, 2, 0, 0]),
    (![0, 0, 0, 0, 1, 1, 2, 2], ![1, 1, 1, 1, 0, 0, 2, 2]),
    (![0, 0, 0, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 2, 2, 2, 2]),
    (![0, 0, 0, 0, 1, 2, 2, 2], ![1, 1, 1, 1, 2, 0, 0, 0]),
    (![0, 0, 0, 1, 1, 1, 2, 2], ![1, 1, 1, 0, 0, 0, 2, 2]),
    (![0, 0, 0, 1, 1, 1, 1, 2], ![1, 1, 1, 2, 2, 2, 2, 0]),
    (![0, 0, 0, 1, 2, 2, 2, 2], ![1, 1, 1, 2, 0, 0, 0, 0]),
    (![0, 0, 0, 2, 2, 2, 2, 2], ![1, 1, 1, 2, 2, 2, 2, 2]),
    (![0, 0, 1, 1, 1, 1, 2, 2], ![1, 1, 0, 0, 0, 0, 2, 2]),
    (![0, 0, 1, 2, 2, 2, 2, 2], ![1, 1, 0, 2, 2, 2, 2, 2]),
    (![0, 0, 1, 1, 1, 1, 2, 2], ![1, 1, 2, 2, 2, 2, 0, 0]),
    (![0, 0, 1, 2, 2, 2, 2, 2], ![1, 1, 2, 0, 0, 0, 0, 0]),
    (![0, 1, 1, 1, 1, 1, 2, 2], ![1, 0, 0, 0, 0, 0, 2, 2]),
    (![0, 1, 1, 2, 2, 2, 2, 2], ![1, 0, 0, 2, 2, 2, 2, 2]),
    (![0, 1, 1, 1, 1, 1, 1, 1], ![1, 2, 2, 2, 2, 2, 2, 2]),
    (![0, 1, 1, 1, 1, 2, 2, 2], ![1, 2, 2, 2, 2, 0, 0, 0]),
    (![0, 1, 2, 2, 2, 2, 2, 2], ![1, 2, 0, 0, 0, 0, 0, 0]),
    (![1, 1, 1, 1, 1, 1, 1, 2], ![0, 0, 0, 0, 0, 0, 0, 1]),
    (![1, 1, 1, 1, 1, 1, 2, 2], ![0, 0, 0, 0, 0, 0, 2, 2]),
    (![1, 1, 1, 1, 2, 2, 2, 2], ![0, 0, 0, 0, 1, 1, 1, 1]),
    (![1, 1, 1, 2, 2, 2, 2, 2], ![0, 0, 0, 2, 2, 2, 2, 2]),
    (![1, 2, 2, 2, 2, 2, 2, 2], ![0, 1, 1, 1, 1, 1, 1, 1]),
    (![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1]),
    (![1, 1, 1, 1, 1, 1, 1, 2], ![1, 1, 1, 1, 1, 1, 1, 2]),
    (![1, 1, 1, 1, 1, 1, 2, 2], ![1, 1, 1, 1, 1, 1, 2, 2]),
    (![1, 1, 1, 1, 1, 2, 2, 2], ![1, 1, 1, 1, 1, 2, 2, 2]),
    (![1, 1, 1, 1, 2, 2, 2, 2], ![1, 1, 1, 1, 2, 2, 2, 2])
  ]

end Certificates.SUSmall

end
