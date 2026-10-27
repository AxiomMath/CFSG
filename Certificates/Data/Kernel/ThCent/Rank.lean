module

public import Certificates.Data.Kernel.ThCent.List

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.BigS

@[expose] noncomputable def rank7OK (c rm ONE : Nat) (V : Nat → Nat) (Y : Nat) (w : List Nat) :
    Bool :=
  strictF (wordR c rm ONE V w) fun E =>
    Bool.or (neB c rm ONE (mulB c rm E Y) (mulB c rm Y E))
      (Nat.beq (powB c rm ONE E 7 (nat_lit 3)) ONE)

@[expose] noncomputable def ord4OK (c rm ONE : Nat) (V : Nat → Nat) (w : List Nat) : Bool :=
  strictF (wordR c rm ONE V w) fun E => strictF (mulB c rm E E) fun E2 =>
    andB (Nat.beq (mulB c rm E2 E2) ONE) (neB c rm ONE E2 ONE)

end CFSG.KC.ThCent

end
