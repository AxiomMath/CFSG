module

public import Certificates.Data.Kernel.MonsterB.U6Orb

public section

namespace CFSG.KC.QForm

open CFSG.KLie.CT CFSG.KC.U6Orb

@[expose] noncomputable def parK (x : Nat) : Nat :=
  xorK (nat_lit 22) fun t => Nat.land (Nat.shiftRight x t) (nat_lit 1)

@[expose] noncomputable def betaK (U x y : Nat) : Nat := parK (Nat.land y (actK U x))

@[expose] noncomputable def qK (U x : Nat) : Nat := betaK U x x

@[expose] noncomputable def bK (U x y : Nat) : Nat := Nat.xor (betaK U x y) (betaK U y x)

@[expose] noncomputable def invK (U M : Nat) : Bool :=
  allN (nat_lit 22) fun a => andB
    (Nat.beq (qK U (fget M a (nat_lit 22))) (qK U (pw2 a)))
    (allN (nat_lit 22) fun b =>
      Nat.beq (bK U (fget M a (nat_lit 22)) (fget M b (nat_lit 22))) (bK U (pw2 a) (pw2 b)))

@[expose] noncomputable def actB (T : Nat → Nat) (k v : Nat) : Nat :=
  Nat.xor (fget (T (Nat.mul (nat_lit 3) k)) (Nat.land v (nat_lit 255)) (nat_lit 22))
    (Nat.xor (fget (T (Nat.add (Nat.mul (nat_lit 3) k) (nat_lit 1)))
        (Nat.land (Nat.shiftRight v (nat_lit 8)) (nat_lit 255)) (nat_lit 22))
      (fget (T (Nat.add (Nat.mul (nat_lit 3) k) (nat_lit 2))) (Nat.shiftRight v (nat_lit 16))
        (nat_lit 22)))

@[expose] noncomputable def tabOK (T M : Nat → Nat) (ng : Nat) : Bool :=
  allN ng fun k => andB
    (allN (nat_lit 256) fun x =>
      Nat.beq (fget (T (Nat.mul (nat_lit 3) k)) x (nat_lit 22)) (actK (M k) x))
    (andB (allN (nat_lit 256) fun x =>
        Nat.beq (fget (T (Nat.add (Nat.mul (nat_lit 3) k) (nat_lit 1))) x (nat_lit 22))
          (actK (M k) (Nat.shiftLeft x (nat_lit 8))))
      (allN (nat_lit 64) fun x =>
        Nat.beq (fget (T (Nat.add (Nat.mul (nat_lit 3) k) (nat_lit 2))) x (nat_lit 22))
          (actK (M k) (Nat.shiftLeft x (nat_lit 16)))))

end CFSG.KC.QForm

end
