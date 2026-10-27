module

public import Certificates.Data.Kernel.Co1Seven.Cen

public section

namespace CFSG.KC.Co1ClosP

open CFSG.KC.Enum CFSG.KS CFSG.KC.Co1B CFSG.KS.SporSch.M24

@[expose] noncomputable def powLK (x : Nat) (es : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun e _ ih y => strictN (powWK y e) ih) es x

@[expose] noncomputable def tgtPK (x : Nat) (es : List Nat) : Bool :=
  bAnd(bIf(Nat.beq x idM, false, true), eqU (powLK x es) idM)

@[expose] noncomputable def witPK (P : Nat → Nat) (N p m x w : Nat) : Bool :=
  strictB (fld16 w 0) fun a => strictB (fld16 w 1) fun ai => strictB (fld16 w 2) fun b =>
  strictB (fld16 w 3) fun bi =>
  bAnd(Nat.blt a N, bAnd(Nat.blt ai N, bAnd(Nat.blt b N, bAnd(Nat.blt bi N,
  bAnd(Nat.beq (mulWK (P a) (P ai)) idM, bAnd(Nat.beq (mulWK (P b) (P bi)) idM,
  strictB (mulWK (mulWK x (mulWK (mulWK (P a) x) (P ai)))
      (powWK (mulWK (mulWK (P b) x) (P bi)) m)) fun y =>
    bAnd(bIf(eqU y idM, false, true), Nat.beq (powWK y p) idM)))))))

@[expose] noncomputable def closPK (P : Nat → Nat) (N : Nat) (es : List Nat) (p m : Nat)
    (R C W : Nat → Nat) : Bool :=
  allN N fun k => strictB (P k) fun x => strictB (R k) fun r =>
    bAnd(bIf(tgtPK x es, strictB (C k) fun c =>
      bAnd(Nat.blt (nat_lit 0) r, bAnd(Nat.blt r N, bAnd(Nat.blt c N, bAnd(Nat.beq (R r) r,
        Nat.beq (mulWK x (P c)) (mulWK (P c) (P r)))))), true),
      bIf(bAnd(Nat.beq r k, Nat.blt (nat_lit 0) k), witPK P N p m x (W k), true))

end CFSG.KC.Co1ClosP

end
