module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KC.He3168

open CFSG.KC.Enum

@[expose] noncomputable def colK (Q t c : Nat) : Bool :=
  allN (nat_lit 50) fun i =>
    Nat.beq (Nat.land (Nat.shiftRight Q (Nat.add (Nat.mul (nat_lit 600) i) (Nat.mul (nat_lit 12) t)))
        (nat_lit 4095))
      (Nat.land (Nat.shiftRight c (Nat.mul (nat_lit 12) i)) (nat_lit 4095))

end CFSG.KC.He3168

end
