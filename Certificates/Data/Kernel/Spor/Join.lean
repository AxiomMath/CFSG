module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.Join

open CFSG.KC.Enum

@[expose] noncomputable def joinOf (c b : Nat) (Fc : Nat → Nat) (j : Nat) : Nat :=
  foldN c (fun i s => Nat.lor s (Nat.shiftLeft (Fc (Nat.add (Nat.mul c j) i)) (Nat.mul b i)))
    (nat_lit 0)

@[expose] noncomputable def joinK (c b : Nat) (Fc F : Nat → Nat) (N : Nat) : Bool :=
  allN N (fun j => bAnd(
    allN c (fun i => Nat.beq (Nat.shiftRight (Fc (Nat.add (Nat.mul c j) i)) b) (nat_lit 0)),
    Nat.beq (F j) (joinOf c b Fc j)))

end CFSG.KS.Join

end
