module

public import CFSG.Certificates.Kernel.Orders.Mat3

public section

namespace CFSG.KC.ONOut

open CFSG.KC.Loop CFSG.KC.Ord

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def d27 (c : Nat) : Nat :=
  nIf(Nat.blt c (nat_lit 58), Nat.sub c (nat_lit 48), Nat.sub c (nat_lit 55))

@[expose] noncomputable def bitK (M p : Nat) : Nat := Nat.land (Nat.shiftRight M p) (nat_lit 1)

@[expose] noncomputable def tritOK (s n N M k t : Nat) : Bool :=
  bIf(Nat.blt k n,
    andB (Nat.beq (bitK M (Nat.mul s k)) (Nat.mod t (nat_lit 2)))
      (Nat.beq (bitK M (Nat.add N (Nat.mul s k))) (Nat.div t (nat_lit 2))),
    true)

@[expose] noncomputable def charOK (s n N M q c : Nat) : Bool :=
  (fun v k => andB (tritOK s n N M k (Nat.mod v (nat_lit 3)))
      (andB (tritOK s n N M (Nat.succ k) (Nat.mod (Nat.div v (nat_lit 3)) (nat_lit 3)))
        (tritOK s n N M (Nat.succ (Nat.succ k)) (Nat.mod (Nat.div v (nat_lit 9)) (nat_lit 3)))))
    (d27 c) (Nat.mul (nat_lit 3) q)

@[expose] noncomputable def run27 (s n N M : Nat) (cs : List Char) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun q => Nat.ble n (Nat.mul (nat_lit 3) q))
    (fun ch _ ih q => (fun c => andB (Nat.blt c (nat_lit 128))
        (andB (charOK s n N M q c) (strictB (Nat.succ q) ih)))
      (Char.toNat ch))
    cs

@[expose] noncomputable def addM3 (N LO X Y : Nat) : Nat :=
  add3 N (Nat.land X LO) (Nat.shiftRight X N) (Nat.land Y LO) (Nat.shiftRight Y N)

@[expose] noncomputable def negM3 (N LO X : Nat) : Nat :=
  Nat.add (Nat.shiftRight X N) (Nat.shiftLeft (Nat.land X LO) N)

@[expose] noncomputable def colM3 (CC X t : Nat) : Nat := Nat.land (Nat.shiftRight X t) CC

@[expose] noncomputable def spinK (mul : Nat → Nat → Nat) (G0 G1 S CC : Nat) (par lab : Nat → Nat)
    (lo n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB ih ((fun t => Nat.beq (mul (nIf(Nat.beq (lab t) (nat_lit 0), G0, G1))
      (colM3 CC S (par t))) (colM3 CC S t)) (Nat.add lo i))) n

end CFSG.KC.ONOut

end
