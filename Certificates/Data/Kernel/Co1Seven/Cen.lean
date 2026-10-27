module

public import Certificates.Data.Kernel.SporSch.Co1Mat
public import Certificates.Data.Kernel.Co1BW

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS CFSG.KC.Co1B

@[expose] noncomputable def eqU (X Y : Nat) : Bool :=
  Nat.beq (Nat.mod X (Nat.shiftLeft (nat_lit 1) (nat_lit 576)))
    (Nat.mod Y (Nat.shiftLeft (nat_lit 1) (nat_lit 576)))

@[expose] noncomputable def tgtK (x : Nat) : Bool :=
  bAnd(bIf(Nat.beq x idM, false, true), strictB (mulWK x x) fun x2 => strictB (mulWK x2 x) fun x3 =>
    bIf(eqU x2 idM, true, bIf(eqU x3 idM, true, eqU (mulWK (mulWK x2 x2) x) idM)))

@[expose] noncomputable def fld16 (w i : Nat) : Nat :=
  Nat.land (Nat.shiftRight w (Nat.mul (nat_lit 16) i)) (nat_lit 65535)

@[expose] noncomputable def wit7K (P : Nat → Nat) (N x w : Nat) : Bool :=
  strictB (fld16 w 0) fun a => strictB (fld16 w 1) fun ai => strictB (fld16 w 2) fun b =>
  strictB (fld16 w 3) fun bi =>
  bAnd(Nat.blt a N, bAnd(Nat.blt ai N, bAnd(Nat.blt b N, bAnd(Nat.blt bi N,
  bAnd(Nat.beq (mulWK (P a) (P ai)) idM, bAnd(Nat.beq (mulWK (P b) (P bi)) idM,
  strictB (mulWK (mulWK x (mulWK (mulWK (P a) x) (P ai))) (mulWK (mulWK (P b) x) (P bi))) fun y =>
    bAnd(bIf(eqU y idM, false, true), Nat.beq (powWK y 7) idM)))))))

@[expose] noncomputable def closK (P : Nat → Nat) (N : Nat) (R C W : Nat → Nat) : Bool :=
  allN N fun k => strictB (P k) fun x => strictB (R k) fun r =>
    bAnd(bIf(tgtK x, strictB (C k) fun c =>
      bAnd(Nat.blt (nat_lit 0) r, bAnd(Nat.blt r N, bAnd(Nat.blt c N, bAnd(Nat.beq (R r) r,
        Nat.beq (mulWK x (P c)) (mulWK (P c) (P r)))))), true),
      bIf(bAnd(Nat.beq r k, Nat.blt (nat_lit 0) k), wit7K P N x (W k), true))

@[expose] noncomputable def commGK (G : Nat → Nat) (ng X : Nat) : Bool :=
  allN ng fun l => Nat.beq (mulWK (G l) X) (mulWK X (G l))

@[expose] noncomputable def centK (P : Nat → Nat) (N Z : Nat) : Bool :=
  allN N fun k => strictB (P k) fun e =>
    bIf(eqU (mulWK e Z) (mulWK Z e), Nat.beq (powWK e 7) idM, true)

end CFSG.KS.SporSch.M24

end
