module

public import Certificates.Data.Kernel.J4Q.QT2A

public section

namespace CFSG.KC.J4Q

open CFSG.KC.Loop

@[expose] noncomputable def bitsJ (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.lor acc (Nat.shiftLeft (nat_lit 1) j)) (f j))
    (nat_lit 112)

@[expose] noncomputable def powFuelK (c rm one : Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => one)
    (fun _ ih M e => Bool.rec (motive := fun _ => Nat)
      (strictN (ih (mulJ c rm M M) (Nat.div e (nat_lit 2))) fun r =>
        Bool.rec (motive := fun _ => Nat) r (mulJ c rm M r) (Nat.beq (Nat.mod e (nat_lit 2)) (nat_lit 1)))
      one (Nat.beq e (nat_lit 0)))
    fuel

end CFSG.KC.J4Q

end
