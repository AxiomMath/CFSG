module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.YModel.Text

public section

namespace CFSG.KC.TitsOuter

open CFSG.KC.Enum
open CFSG.KC.YModel (fieldAt lget)

@[expose] noncomputable def labAt (F p : Nat) : Nat := fieldAt (nat_lit 32) F p

@[expose] noncomputable def partK (F : Nat) (A B : List Nat) (p : Nat) : Nat :=
  strictN (labAt F p) fun v => nIf(Nat.beq p (lget A v), lget B v, lget A v)

@[expose] noncomputable def labOK (n F : Nat) (A B : List Nat) : Bool :=
  allN n fun p => bIf(Nat.beq p (nat_lit 0), true,
    strictB (partK F A B p) fun q => bAnd(Nat.blt q n,
      bAnd(Bool.rec (motive := fun _ => Bool) true false (Nat.beq q p),
        Nat.beq (labAt F q) (labAt F p))))

end CFSG.KC.TitsOuter

end
