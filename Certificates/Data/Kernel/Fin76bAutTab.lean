module

public import Certificates.Data.Kernel.Fin76bAutFacts

public section

namespace CFSG.KS.EAut

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Row CFSG.KS.PEnum

@[expose] noncomputable def eNcm (ET : Nat → Nat) (y x : Nat) : Bool :=
  bIf(eCm ET y x, false, true)

@[expose] noncomputable def e69TabK (ET : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 32) (fun k => eZ (eMul ET k k)),
  bAnd(Nat.beq (eCnt (nat_lit 32) (fun k => eKind ET (nat_lit 0) k)) (nat_lit 10),
  bAnd(Nat.beq (eCnt (nat_lit 32) (fun k => Nat.beq (eMul ET k k) (nat_lit 21))) (nat_lit 20),
    allN (nat_lit 32) (fun x => bIf(eKind ET (nat_lit 0) x,
      bAnd(Nat.beq (eCnt (nat_lit 32) (fun y => bAnd(eKind ET (nat_lit 0) y, eNcm ET y x)))
          (nat_lit 8),
        Nat.beq (eCnt (nat_lit 32) (fun y => bAnd(Nat.beq (eMul ET y y) (nat_lit 21), eNcm ET y x)))
          (nat_lit 8)), true)))))

end CFSG.KS.EAut

end
