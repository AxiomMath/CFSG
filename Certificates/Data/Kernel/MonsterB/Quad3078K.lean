module

public import Certificates.Data.Kernel.BabyMonster.CTIB.OrbTreeW

public section

namespace CFSG.KC.Q3078

open CFSG.KC.BM

@[expose] noncomputable def byteK (R i : Nat) : Nat :=
  Nat.land (Nat.shiftRight R (Nat.mul (nat_lit 8) i)) (nat_lit 255)

@[expose] noncomputable def bitK (n j : Nat) : Nat := Nat.land (Nat.shiftRight n j) (nat_lit 1)

@[expose] noncomputable def xorK (R base n m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.xor acc (Nat.mul (bitK n j) (byteK R (Nat.add base j)))) m

@[expose] noncomputable def affK (RW CK k n : Nat) : Nat :=
  Nat.xor (byteK CK k) (xorK RW (Nat.mul (nat_lit 8) k) n (nat_lit 8))

@[expose] noncomputable def pairK (RW CK k p : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 256) (affK RW CK k (Nat.div p (nat_lit 256))))
    (affK RW CK k (Nat.mod p (nat_lit 256)))

@[expose] noncomputable def zdK (ZM p : Nat) : Bool :=
  andB (Nat.beq (bitK ZM (Nat.div p (nat_lit 256))) (nat_lit 1))
    (andB (Nat.beq (bitK ZM (Nat.mod p (nat_lit 256))) (nat_lit 1))
      (notB (Nat.beq (Nat.div p (nat_lit 256)) (Nat.mod p (nat_lit 256)))))

@[expose] noncomputable def cntK (ZM n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun j acc => Nat.add acc (bitK ZM j)) n

@[expose] noncomputable def keepK (RW CK ZM t : Nat) : Bool :=
  Nat.beq (bitK ZM (affK RW CK (Nat.div t (nat_lit 256)) (Nat.mod t (nat_lit 256))))
    (bitK ZM (Nat.mod t (nat_lit 256)))

end CFSG.KC.Q3078

end
