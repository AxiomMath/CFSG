module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.LySeed

open CFSG.KC.Enum

@[expose] noncomputable def laneR (X i : Nat) : Nat :=
  fld(X, Nat.mul (nat_lit 1332) i, Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1332)) (nat_lit 1))

@[expose] noncomputable def laneE (X i j : Nat) : Nat :=
  fld(laneR X i, Nat.mul (nat_lit 12) j, nat_lit 4095)

@[expose] noncomputable def entK (X : Nat) (f : Nat → Nat → Nat) : Bool :=
  allN (nat_lit 111) (fun i => allN (nat_lit 111) (fun j => Nat.beq (laneE X i j) (f i j)))

@[expose] noncomputable def trK (X Y : Nat) : Bool := entK Y (fun i j => laneE X j i)

@[expose] noncomputable def symK (X : Nat) : Bool := trK X X

end CFSG.KC.LySeed

end
