module

public import Certificates.Data.Kernel.G24Key

public section

namespace CFSG.KC.G24Key

open CFSG.KC.Enum

@[expose] noncomputable def cosK (S TP TG : Nat → Nat) (fuel T k p : Nat) : Nat :=
  downK S TP TG fuel k (ap T p)

@[expose] noncomputable def recO (S TP TG : Nat → Nat) (fuel T A B R k r : Nat) : Bool :=
  bIf(Nat.beq (Nat.land r (nat_lit 1)) (nat_lit 0),
    strictB (Nat.shiftRight r (nat_lit 1)) (fun b => bAnd(Nat.blt b (nat_lit 3),
      bIf(Nat.beq (cosK S TP TG fuel T k (cosK S TP TG fuel T k b)) b, false, true))),
    strictB fld(r, nat_lit 2, nat_lit 255) (fun L =>
    strictB (Nat.shiftRight r (nat_lit 10)) (fun W =>
    allN (nat_lit 3) (fun b => Nat.beq (wpt A B W L (cosK S TP TG fuel T k b))
      (ap R (wpt A B W L b))))))

@[expose] noncomputable def ptsK (f : Nat → Nat) (k : Nat) : Bool :=
  allN (nat_lit 3) (fun b => Nat.beq (f b) (kpt k b))

@[expose] noncomputable def fixK (S : Nat → Nat) (J n : Nat) : Bool :=
  allN n (fun q => bIf(Nat.beq q (nat_lit 0), true,
    bIf(allN J (fun j => bIf(bAnd(Nat.beq (ap (S j) (nat_lit 0)) (nat_lit 0),
      bIf(Nat.beq (ap (S j) q) q, false, true)), false, true)), false, true)))

end CFSG.KC.G24Key

end
