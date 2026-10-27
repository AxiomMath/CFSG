module

public import Certificates.Data.Kernel.Hall82K.Rm
public import Certificates.Data.Kernel.Hall82K.C5

public section

namespace CFSG.KC.Hall82K

open CFSG.KC.Ord CFSG.KC.LQT

@[expose] def fixAtK (b c : Nat) : Bool := Nat.beq (apL c b) b

@[expose] noncomputable def transAtK (EL : Nat → Nat) (T v : Nat) : Bool :=
  P.letB (lane T 11 2047 v) fun w =>
    andB (Nat.blt w 1080)
      (andB (P.impB (inKK v) (Nat.beq (apL (EL w) 1) v))
        (orB (inKK v) (orB (Nat.beq v 0) (Nat.beq (apL (EL w) 5) v))))

@[expose] noncomputable def kIffK (g : Nat) : Bool :=
  P.allN 64 fun v => beqB (inKK v) (inKK (apL g v))

@[expose] noncomputable def nvWitOK (EL : Nat → Nat) (x r : Nat) : Bool :=
  P.letB (Nat.land r 2047) fun w => P.letB (Nat.shiftRight r 11) fun wi =>
    andB (Nat.blt w 1080) (andB (Nat.blt wi 1080) (andB (fixAtK 1 (EL w))
      (andB (Nat.beq (compL (EL w) (EL wi)) idK)
        (negK (Nat.beq (powL (compL x (powL (compL (compL (EL w) x) (EL wi)) 15)) 16) idK)))))

@[expose] noncomputable def nvAtOK (E EL : Nat → Nat) (W k : Nat) : Bool :=
  P.letB (E k) fun x =>
    P.impB (andB (fixAtK 1 x) (andB (negK (Nat.beq x idK)) (Nat.beq (powL x 16) idK)))
      (nvWitOK EL x (lane W 22 4194303 k))

@[expose] noncomputable def lgenMemK (E : Nat → Nat) (I g0 g1 : Nat) : Bool :=
  andB (andB (Nat.blt (lane I 12 4095 0) 2160) (Nat.beq (E (lane I 12 4095 0)) g0))
    (andB (Nat.blt (lane I 12 4095 1) 2160) (Nat.beq (E (lane I 12 4095 1)) g1))

@[expose] noncomputable def zetaK (z : Nat) : Bool :=
  andB (permK z) (P.allN 64 fun v => orB (Nat.beq v 0) (negK (Nat.beq (apL z v) v)))

end CFSG.KC.Hall82K
