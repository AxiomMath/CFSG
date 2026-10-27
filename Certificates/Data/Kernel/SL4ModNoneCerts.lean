module

public import Certificates.Data.Kernel.SL4ModClassCerts
public import Certificates.Data.SL4ModNoneData

public section

namespace CFSG.LargeExtraspecial.SL4Mod.Native

open CFSG.Sporadic.SmallF2.Native

structure NoneRec where
  L : List Nat
  src : List (Nat × Nat)
  e : Nat
  masks : List Nat
  piv : List Nat
  sel : Nat
  B : List Nat
  coef : List Nat
  mB : Nat
  pair : Nat
deriving Inhabited

abbrev NoneTup : Type := List Nat × List (Nat × Nat) × Nat × List Nat × List Nat × Nat ×
  List Nat × List Nat × Nat × Nat

@[expose] def mkNoneRec (x : NoneTup) : NoneRec :=
  { L := x.1, src := x.2.1, e := x.2.2.1, masks := x.2.2.2.1, piv := x.2.2.2.2.1,
    sel := x.2.2.2.2.2.1, B := x.2.2.2.2.2.2.1, coef := x.2.2.2.2.2.2.2.1,
    mB := x.2.2.2.2.2.2.2.2.1, pair := x.2.2.2.2.2.2.2.2.2 }

@[expose] def mkNoneEntry (x : Nat × NoneTup × NoneTup) : Nat × NoneRec × NoneRec :=
  (x.1, mkNoneRec x.2.1, mkNoneRec x.2.2)

@[expose] def onesV : Nat := 2 ^ 105 - 1

@[expose] def coverOwn (e nB : Nat) : Bool :=
  noneDims.all fun d => decide (d + 1 ≤ e) || (decide (0 < nB) && decide (nB < d))

@[expose] def coverPartner (c : NoneRec) : Bool :=
  noneDims.all fun d => decide (d + 2 ≤ c.e) ||
    (decide (0 < c.B.length) && nz (xorSelL c.sel (c.L.map (· ^^^ onesV))) &&
      decide (c.B.length + 1 < d))

@[expose] def noneCL (tl : List (List Nat)) (x : Nat) (c : NoneRec) : Bool :=
  derivOKL tl x c.L c.src && echOKL c.e c.L c.masks c.piv &&
    (c.B.isEmpty || (nz (xorSelL c.sel c.L) && xorSelL c.mB c.B == xorSelL c.sel c.L &&
      closedCL tl c.B c.coef)) &&
    coverOwn c.e c.B.length && (c.pair != 1 || coverPartner c)

@[expose] def entryOK (tl : List (List Nat)) (a b : Nat) (ent : Nat × NoneRec × NoneRec) : Bool :=
  let x₁ := if ent.1 == 0 then a else b
  let x₂ := if ent.1 == 0 then b else a
  noneCL tl x₁ ent.2.1 &&
    (!nz x₂ || (ent.2.1.pair == 1 && x₁ ^^^ x₂ == onesV) || noneCL tl x₂ ent.2.2)

@[expose] def checkNoneFrom (tl : List (List Nat)) (od : OrbData) :
    Nat → List (Nat × NoneRec × NoneRec) → Bool
  | _, [] => true
  | n, ent :: es => entryOK tl (expandL od.lab.toList (64 + n)) (expandL od.lab.toList (63 - n)) ent &&
      checkNoneFrom tl od (n + 1) es

@[expose] def onesFixedL (tl : List (List Nat)) : Bool :=
  (List.range 6).all fun s => actVL (tl.getD s []) onesV == onesV

end CFSG.LargeExtraspecial.SL4Mod.Native
