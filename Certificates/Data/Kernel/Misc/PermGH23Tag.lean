module

public import Certificates.Data.Kernel.Misc.PermGH23

public section

namespace CFSG.KC.Misc.GH23

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def commAt (EA : Nat → Nat) (nA : Nat) (EB : Nat → Nat) (nB : Nat)
    (W : Nat → Nat) (o i : Nat) : Bool :=
  letB (W (Nat.add o i)) fun t => letB (EA (Nat.div i nA)) fun x => letB (EA (Nat.mod i nA)) fun y =>
    andB (Nat.blt t nB) (Nat.beq (mul8 (EB t) (mul8 y x)) (mul8 x y))

@[expose] noncomputable def memAt (E : Nat → Nat) (N c t : Nat) : Bool :=
  andB (Nat.blt t N) (Nat.beq (E t) c)

end CFSG.KC.Misc.GH23

end
