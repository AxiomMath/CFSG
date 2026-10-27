module

public import Certificates.Data.Kernel.G2Three.K7b
public import Certificates.Data.G2GenCheck

public section

namespace CFSG.KD.G2Three

open Certificates.G2Gen

@[expose] noncomputable def powK (a : Nat) : Nat → Nat
  | 0 => ONE
  | n + 1 => MUL a (powK a n)

@[expose] noncomputable def g2GenK (G : Nat → Nat) : Bool :=
  let W := k7bWord G
  let d := W dW
  let yi := W yInW
  let yo := W yOutW
  Nat.beq (MUL d d) ONE && Nat.testBit d (196 + 45) &&
    Nat.beq (MUL (W gW) (W giW)) ONE &&
    Nat.beq (powK yi 13) ONE && nzK yi 2 &&
    Nat.beq (MUL (W g1W) (W g1iW)) ONE &&
    Nat.beq (MUL (W g2W) (W g2iW)) ONE &&
    Nat.beq (MUL (W c1W) (W c1iW)) ONE &&
    Nat.beq (powK yo 13) ONE && nzK yo 2

end CFSG.KD.G2Three

end
