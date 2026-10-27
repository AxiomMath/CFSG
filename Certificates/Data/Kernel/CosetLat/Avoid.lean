module

public import Certificates.Data.Kernel.CosetLat.Defs

public section

namespace CFSG.KC.CosetLat

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def allCosAt (M : Nat → Nat → Nat) (ET : Nat → Nat) (nT : Nat)
    (EU : Nat → Nat) (P : Nat → Bool) (i : Nat) : Bool :=
  allN nT fun k => P (M (ET k) (EU i))

@[expose] noncomputable def invPairAt (M : Nat → Nat → Nat) (a a2 b b2 c : Nat) : Bool :=
  notB (andB (Nat.beq (M c a) (M a2 c)) (Nat.beq (M c b) (M b2 c)))

end CFSG.KC.CosetLat

end
