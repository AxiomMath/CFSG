module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.ShortVals

open CFSG.KC.Loop

@[expose] noncomputable def bitK (w k : Nat) : Bool := Nat.beq (fld(w, k, nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def sgnK (w k : Nat) : Nat :=
  nIf(bitK w k, nat_lit 68719476735, nat_lit 1)

@[expose] noncomputable def sumK (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => Nat.add acc (f k)) n

@[expose] noncomputable def allK (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => bAnd(f k, acc)) n

@[expose] noncomputable def letK (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def aK (AP i j : Nat) : Nat :=
  fld(AP, Nat.mul (nat_lit 32) (Nat.add (Nat.mul (nat_lit 24) i) j), nat_lit 4294967295)

@[expose] noncomputable def bmK : Nat :=
  0xaaaa00cccc00c6a0a06ac0c06ca00aa6c00ce111111e111111e111111e111111e111111e

@[expose] noncomputable def wordK (a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun j acc =>
    nIf(bitK a j, Nat.xor acc (fld(bmK, Nat.mul (nat_lit 24) j, nat_lit 16777215)), acc)) (nat_lit 12)

@[expose] noncomputable def wAt (WT t : Nat) : Nat :=
  fld(WT, Nat.mul (nat_lit 24) t, nat_lit 16777215)

@[expose] noncomputable def cAt (OC o t : Nat) : Nat :=
  fld(OC, Nat.add (Nat.mul (nat_lit 40) o) (Nat.mul (nat_lit 5) t), nat_lit 31)

@[expose] noncomputable def eAt (ET m : Nat) : Nat := fld(ET, Nat.mul (nat_lit 8) m, nat_lit 255)

@[expose] noncomputable def pAt (PT q b : Nat) : Nat :=
  fld(PT, Nat.add (Nat.mul (nat_lit 10) q) (Nat.mul (nat_lit 5) b), nat_lit 31)

@[expose] noncomputable def vAt (VP k : Nat) : Nat :=
  fld(VP, Nat.mul (nat_lit 36) k, nat_lit 68719476735)

@[expose] noncomputable def rAt (RP p : Nat) : Nat :=
  fld(RP, Nat.mul (nat_lit 17) p, nat_lit 131071)

@[expose] noncomputable def posOK (VP RP PP p e : Nat) : Bool :=
  letK (rAt RP p) fun r => bAnd(Nat.blt r (nat_lit 98280),
    bAnd(Nat.beq e (vAt VP r), Nat.beq (rAt PP r) p))

@[expose] noncomputable def pairOK (AP PT VP RP PP q : Nat) : Bool :=
  letK (pAt PT q (nat_lit 0)) fun a =>
  letK (pAt PT q (nat_lit 1)) fun c =>
  letK (Nat.add (Nat.mul (nat_lit 16) (aK AP a a)) (Nat.mul (nat_lit 16) (aK AP c c))) fun S =>
  bAnd(posOK VP RP PP (Nat.mul (nat_lit 2) q)
      (Nat.mod (Nat.add S (Nat.mul (nat_lit 2199023255520) (aK AP a c))) (nat_lit 68719476736)),
    posOK VP RP PP (Nat.add (Nat.mul (nat_lit 2) q) (nat_lit 1))
      (Nat.mod (Nat.add S (Nat.mul (nat_lit 32) (aK AP a c))) (nat_lit 68719476736)))

@[expose] noncomputable def asK (AP w i : Nat) : Nat :=
  sumK (nat_lit 24) fun k => Nat.mul (aK AP i k) (sgnK w k)

@[expose] noncomputable def qK (AP w : Nat) : Nat :=
  sumK (nat_lit 24) fun i => Nat.mul (sgnK w i) (asK AP w i)

@[expose] noncomputable def eOdd (AP w Q i : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.add Q (Nat.mul (nat_lit 549755813880) (Nat.mul (sgnK w i) (asK AP w i))))
    (Nat.mul (nat_lit 16) (aK AP i i))) (nat_lit 68719476736)

@[expose] noncomputable def oddOK (AP WT VP RP PP t : Nat) : Bool :=
  letK (wAt WT t) fun w =>
  letK (qK AP w) fun Q =>
  allK (nat_lit 24) fun i =>
    posOK VP RP PP (Nat.add (Nat.add (nat_lit 552) (Nat.mul (nat_lit 24) t)) i) (eOdd AP w Q i)

@[expose] noncomputable def awK (AP w k : Nat) : Nat :=
  sumK (nat_lit 24) fun j => nIf(bitK w j, aK AP k j, nat_lit 0)

@[expose] noncomputable def wwK (AP w : Nat) : Nat :=
  sumK (nat_lit 24) fun k => nIf(bitK w k, awK AP w k, nat_lit 0)

@[expose] noncomputable def xK8 (AP OC o w m : Nat) : Nat :=
  sumK (nat_lit 8) fun a => nIf(bitK m a, awK AP w (cAt OC o a), nat_lit 0)

@[expose] noncomputable def yK8 (AP OC o m : Nat) : Nat :=
  sumK (nat_lit 8) fun a => nIf(bitK m a, sumK (nat_lit 8) fun b =>
    nIf(bitK m b, aK AP (cAt OC o a) (cAt OC o b), nat_lit 0), nat_lit 0)

@[expose] noncomputable def eOct (W X Y : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.add (Nat.mul (nat_lit 4) W) (Nat.mul (nat_lit 1099511627760) X))
    (Nat.mul (nat_lit 16) Y)) (nat_lit 68719476736)

@[expose] noncomputable def octOK (AP OWT OC ET VP RP PP o : Nat) : Bool :=
  letK (wAt OWT o) fun w =>
  letK (wwK AP w) fun W =>
  allK (nat_lit 64) fun m =>
    letK (eAt ET m) fun m' =>
    posOK VP RP PP (Nat.add (Nat.add (nat_lit 49704) (Nat.mul (nat_lit 64) o)) m)
      (eOct W (xK8 AP OC o w m') (yK8 AP OC o m'))

@[expose] noncomputable def incOK (VP k : Nat) : Bool :=
  Nat.blt (vAt VP k) (vAt VP (Nat.add k (nat_lit 1)))

end CFSG.KC.ShortVals

end
