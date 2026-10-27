module

public import Certificates.Data.Kernel.TwistDce3.Cover

public section

namespace CFSG.KC.TwDce3

open CFSG.KC.TwDce2 (allRange)

@[expose] noncomputable def tupleOK (PO : Nat) (FO : Nat → Nat) (PB : Nat) (F TU : Nat → Nat)
    (BS NB NL NP NQ : Nat) : Bool :=
  CFSG.KC.andB (Nat.beq (TU (nat_lit 0)) BS)
    (allRange (fun p => CFSG.KC.andB
      (allRange (fun i => Nat.blt (CFSG.KC.TwDce.fld (TU p) (Nat.mul (nat_lit 16) i) (nat_lit 65535))
        NQ) (nat_lit 0) NB)
      (allRange (fun c => allRange (fun i =>
        Nat.beq (CFSG.KC.TwDce.fld (TU (CFSG.KC.YModel.fieldAt PO (FO c) p))
            (Nat.mul (nat_lit 16) i) (nat_lit 65535))
          (CFSG.KC.YModel.fieldAt PB (F c)
            (CFSG.KC.TwDce.fld (TU p) (Nat.mul (nat_lit 16) i) (nat_lit 65535))))
        (nat_lit 0) NB) (nat_lit 0) NL)) (nat_lit 0) NP)

end CFSG.KC.TwDce3

end
