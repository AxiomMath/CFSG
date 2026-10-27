module

public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Fin.Basic

public section

namespace Certificates.S7Twin

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

@[expose] def parseWords (s : String) : List (List Int) :=
  let s' := String.ofList (s.toList.filter fun c => !c.isWhitespace)
  (s'.splitOn ";").map fun w => ((w.splitOn ",").filter (· ≠ "")).map String.toInt!

@[expose] def invPairB (n : Nat) (t r : Array Nat) : Bool :=
  (List.range n).all (fun i => decide (t[i]! < n) && r[t[i]!]! == i) &&
    (List.range n).all (fun i => decide (r[i]! < n) && t[r[i]!]! == i)

theorem invPairB_spec {n : Nat} {t r : Array Nat} (h : invPairB n t r = true) :
    (∀ i < n, t[i]! < n ∧ r[t[i]!]! = i) ∧ ∀ i < n, r[i]! < n ∧ t[r[i]!]! = i := by
  simp only [invPairB, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at h
  exact h

@[expose] def permOfInv (n : Nat) (t r : Array Nat) : Equiv.Perm (Fin n) :=
  if h : invPairB n t r = true then
    { toFun := fun x => ⟨t[x.1]!, ((invPairB_spec h).1 x x.2).1⟩
      invFun := fun x => ⟨r[x.1]!, ((invPairB_spec h).2 x x.2).1⟩
      left_inv := fun x => Fin.ext ((invPairB_spec h).1 x x.2).2
      right_inv := fun x => Fin.ext ((invPairB_spec h).2 x x.2).2 }
  else Equiv.refl (Fin n)

@[expose] def spanT (n : Nat) (R Ri Y Yi : Table) : List Table :=
  [idT n, compT n R R, R, Ri, Y, Yi, compT n R Y, compT n Y R]

@[expose] def memT (n : Nat) (L : List Table) (X : Table) : Bool :=
  L.any (tblEq n X)

@[expose] def sqOneT (n : Nat) (A : Table) : Bool :=
  tblEq n (compT n A A) (idT n)

@[expose] def q8PairT (n : Nat) (R Ri Y : Table) : Bool :=
  tblEq n (compT n R R) (compT n Y Y) && tblEq n (compT n R Y) (compT n Y Ri)

@[expose] def q8RelT (n : Nat) (X Xi Y Yi : Table) : Bool :=
  let X2 := compT n X X
  tblEq n (compT n X2 X2) (idT n) && !tblEq n X2 (idT n) && tblEq n X2 (compT n Y Y) &&
    tblEq n (compT n (compT n Yi X) Y) Xi

@[expose] def pairWitT (n : Nat) (sp0 sp : List Table) (R C Ci : Table) : Bool :=
  let J := sp.map (conjT n C Ci)
  J.all (memT n sp0) ||
    (J.any (fun x => !memT n sp x) && sp.any (fun a => !sqOneT n a && memT n J a)) ||
    (memT n J (compT n R R) && sp.all (fun a => sqOneT n a || !memT n J a) &&
      sp.any fun k => J.any fun w => !commT n k w)

@[expose] def repPairsT (n : Nat) (sp0 L4 : List Table) (R : Table)
    (cands : List (Table × Table)) : Bool :=
  let Ri := invT n R
  invOK n R Ri && L4.all fun Y => !q8PairT n R Ri Y ||
    (let Yi := invT n Y
     invOK n Y Yi && cands.any fun c => pairWitT n sp0 (spanT n R Ri Y Yi) R c.1 c.2)

@[expose] def pairsOK (n : Nat) (sp0 L4 reps : List Table) (cands : List (List (Table × Table))) :
    Bool :=
  reps.length == cands.length && (reps.zip cands).all fun p => repPairsT n sp0 L4 p.1 p.2

end Certificates.S7Twin
