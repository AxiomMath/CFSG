module

public import Certificates.Data.Kernel.F2Word

public section

namespace CFSG.KC.S63K

@[expose] noncomputable def lowV (c : Nat) : Nat :=
  bif Nat.blt c 48 then 16 else bif Nat.blt c 58 then c - 48 else
    bif Nat.blt c 97 then 16 else bif Nat.blt c 103 then c - 87 else 16

@[expose] noncomputable def lowK : List Char → Nat → Nat → Bool
  | [], _, _ => true
  | c :: cs, k, D => Nat.blt c.toNat 128 && Nat.blt (lowV c.toNat) 16 &&
      Nat.beq (lowV c.toNat) (Nat.shiftRight D (4 * k) % 16) && lowK cs (k + 1) D

@[expose] noncomputable def dg (D j : Nat) : Nat := Nat.shiftRight D (4 * j) % 16

@[expose] noncomputable def dec3 (D o : Nat) : Nat :=
  ((0 * 16 + dg D o) * 16 + dg D (o + 1)) * 16 + dg D (o + 2)

end CFSG.KC.S63K

end
