module

public import Certificates.Data.Kernel.G2Three.Defs
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KD.G2Three

open CFSG.KC.Loop

@[expose] noncomputable def q16PairK (X : Nat → Nat) (n x z : Nat) : Bool :=
  allBelow n 1 fun u =>
    !(Nat.beq (MUL (X u) (X u)) z) || !(Nat.beq (MUL (MUL x (X u)) x) (X u))

@[expose] noncomputable def q16AtK (X : Nat → Nat) (n x : Nat) : Bool :=
  CFSG.KC.Enum.strictB (MUL x x) fun x2 => CFSG.KC.Enum.strictB (MUL x2 x2) fun x4 =>
    Nat.beq x4 ONE || !(Nat.beq (MUL x4 x4) ONE) || q16PairK X n x x4

@[expose] noncomputable def q16K (X : Nat → Nat) (n : Nat) : Bool :=
  allBelow n 1 fun t => q16AtK X n (X t)

end CFSG.KD.G2Three

end
