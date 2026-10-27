module

public import Certificates.Data.Kernel.O8.SB

public section

namespace CFSG.KC.SBCenF

open CFSG.KC.Enum CFSG.KC.SB

@[expose] noncomputable def rowFN (mul : Nat → Nat → Nat) (NR : Nat → Nat) (W L x : Nat) : Nat :=
  nIf(Nat.blt x (nat_lit 65536),
    strictN (Nat.shiftRight x (nat_lit 7)) fun r => strictN (NR r) fun nr =>
      strictN (Nat.mul (nat_lit 16) (Nat.land x (nat_lit 127))) fun o =>
        mul fld(W, Nat.mul (nat_lit 16) fld(nr, o, nat_lit 127), nat_lit 65535)
          fld(L, Nat.mul (nat_lit 16) fld(nr, Nat.add o (nat_lit 7), nat_lit 511), nat_lit 65535),
    mul fld(W, Nat.mul (nat_lit 16) (nat_lit 0), nat_lit 65535)
      fld(L, Nat.mul (nat_lit 16) (nat_lit 0), nat_lit 65535))

end CFSG.KC.SBCenF

end
