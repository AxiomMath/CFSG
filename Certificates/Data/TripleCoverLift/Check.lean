module

public import Certificates.Data.CFSGNative.SectionRank.Elem3

public section

namespace CFSG.SectionRank.Native

set_option compiler.extract_closed false

inductive LiftRel where
  | inv (n i : Nat)
  | fix (n i : Nat)
  | swap (n i j : Nat)
deriving Inhabited

structure LiftData where
  base : Data
  inv₁ : Nat
  inv₂ : Nat
  units : List (Nat × Nat)
  rels : List LiftRel

namespace LiftData

variable {M V : Type} (O : Ops M V)

@[expose] def conjOK (X T T₁ T₂ : M) : Bool :=
  O.eq (O.mul X T) (O.mul T₁ X) || O.eq (O.mul X T) (O.mul T₂ X) ||
    O.eq (O.mul X T) (O.mul (O.mul T₁ T₂) X)

@[expose] def relOK [Inhabited M] (D : LiftData) (R : Array M) : LiftRel → Bool
  | .inv n i => decide (n < D.base.nregs) && decide (i < D.base.outs.length) &&
      D.units.any (fun u => u.1 == n) &&
      O.eq (O.mul R[n]! R[D.base.outs[i]!]!)
        (O.mul (O.mul R[D.base.outs[i]!]! R[D.base.outs[i]!]!) R[n]!)
  | .fix n i => decide (n < D.base.nregs) && decide (i < D.base.outs.length) &&
      D.units.any (fun u => u.1 == n) &&
      O.eq (O.mul R[n]! R[D.base.outs[i]!]!) (O.mul R[D.base.outs[i]!]! R[n]!)
  | .swap n i j => decide (n < D.base.nregs) && decide (i < D.base.outs.length) &&
      decide (j < D.base.outs.length) && D.units.any (fun u => u.1 == n) &&
      O.eq (O.mul R[n]! R[D.base.outs[i]!]!) (O.mul R[D.base.outs[j]!]! R[n]!) &&
      O.eq (O.mul R[n]! R[D.base.outs[j]!]!) (O.mul R[D.base.outs[i]!]! R[n]!)

@[expose] def check [Inhabited M] (D : LiftData) : Bool :=
  let R := O.run D.base.prog
    (O.initRegs (O.decode D.base.seedA) (O.decode D.base.seedB) D.base.nregs)
  decide (2 ≤ D.base.nregs) && D.base.prog.all (Op.lt D.base.nregs) &&
    D.base.outs.all (decide <| · < D.base.nregs) && decide (D.inv₁ < D.base.nregs) &&
    decide (D.inv₂ < D.base.nregs) &&
    O.elemOK (D.base.outs.map fun r => R[r]!) D.base.tests &&
    O.eq (O.mul R[D.inv₁]! R[D.inv₁]!) O.one && O.eq (O.mul R[D.inv₂]! R[D.inv₂]!) O.one &&
    O.commOK R[D.inv₁]! R[D.inv₂]! &&
    D.base.tests.any (fun k => O.vne (O.vmul (O.unit k) R[D.inv₁]!) (O.unit k)) &&
    D.base.outs.all (fun r => conjOK O R[r]! R[D.inv₁]! R[D.inv₁]! R[D.inv₂]! &&
      conjOK O R[r]! R[D.inv₂]! R[D.inv₁]! R[D.inv₂]!) &&
    D.units.all (fun u => decide (u.1 < D.base.nregs) && decide (0 < u.2) &&
      O.eq (O.pow R[u.1]! u.2) O.one) &&
    D.rels.all (relOK O D R)

end LiftData

end CFSG.SectionRank.Native
