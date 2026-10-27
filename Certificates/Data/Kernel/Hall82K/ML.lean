module

public import Certificates.Data.Kernel.Hall82K.DA

public section

namespace CFSG.KC.Hall82K

open CFSG.KC.Ord CFSG.KC.LQT

@[expose] noncomputable def commK (a b : Nat) : Bool := Nat.beq (compL a b) (compL b a)

@[expose] noncomputable def rootK (E : Nat → Nat) (I g0 g1 : Nat) : Bool :=
  andB (andB (Nat.blt (lane I 12 4095 0) 2160)
      (Nat.beq (compL (E (lane I 12 4095 0)) (E (lane I 12 4095 0))) g0))
    (andB (Nat.blt (lane I 12 4095 1) 2160)
      (Nat.beq (compL (E (lane I 12 4095 1)) (E (lane I 12 4095 1))) g1))

@[expose] noncomputable def centerAtK (EL : Nat → Nat) (Z W k : Nat) : Bool :=
  P.letB (EL k) fun x =>
    orB (orB (Nat.beq x idK) (orB (Nat.beq x Z) (Nat.beq x (compL Z Z))))
      (P.letB (lane W 11 2047 k) fun j => andB (Nat.blt j 1080) (negK (commK x (EL j))))

@[expose] noncomputable def nvWitZK (EL : Nat → Nat) (x r : Nat) : Bool :=
  P.letB (Nat.land r 2047) fun w => P.letB (Nat.shiftRight r 11) fun wi =>
    andB (Nat.blt w 1080) (andB (Nat.blt wi 1080)
      (andB (Nat.beq (compL (EL w) (EL wi)) idK)
        (negK (Nat.beq (powL (compL x (powL (compL (compL (EL w) x) (EL wi)) 15)) 16) idK))))

@[expose] noncomputable def nvAtZK (E EL : Nat → Nat) (W k : Nat) : Bool :=
  P.letB (E k) fun x =>
    P.impB (andB (negK (Nat.beq x idK)) (Nat.beq (powL x 16) idK))
      (nvWitZK EL x (lane W 22 4194303 k))

@[expose] noncomputable def conjTAtK (EL : Nat → Nat) (T W k : Nat) : Bool :=
  P.letB (EL k) fun x =>
    P.impB (andB (negK (Nat.beq x idK)) (Nat.beq (compL x x) idK))
      (P.letB (lane W 22 4194303 k) fun r => P.letB (Nat.land r 2047) fun w =>
        P.letB (Nat.shiftRight r 11) fun wi =>
          andB (Nat.blt w 1080) (andB (Nat.blt wi 1080)
            (andB (Nat.beq (compL (EL w) (EL wi)) idK)
              (Nat.beq (compL (compL (EL w) T) (EL wi)) x))))

@[expose] noncomputable def fix8AtK (E : Nat → Nat) (Z F k : Nat) : Bool :=
  P.letB (E k) fun x =>
    P.impB (andB (Nat.beq (compL x x) idK) (negK (commK x Z)))
      (P.letB (lane F 48 281474976710655 k) fun f =>
        P.allN 64 fun v => P.impB (Nat.beq (apL x v) v)
          (P.anyN 8 fun i => Nat.beq (lane f 6 63 i) v))

end CFSG.KC.Hall82K
