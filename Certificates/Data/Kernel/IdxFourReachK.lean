module

public import Certificates.Data.Kernel.IdxFourOrbitTreeK
public import Certificates.Data.Kernel.IdxFourLbarK

public section

namespace CFSG.KC.IF4W

open CFSG.KC.IF4C CFSG.KC.IF4O CFSG.KC.IF4L

@[expose] noncomputable def nodeP (G D r k : Nat) (P : Nat → Bool) (n : Nat) : Bool :=
  !P n || Nat.beq n r ||
    (Nat.blt (genT D n) k && P (parT D n) && Nat.blt (depT D (parT D n)) (depT D n) &&
      Nat.beq (ap12 (look G (genT D n)) (parT D n)) n)

@[expose] noncomputable def reachOK (G D r k : Nat) (P : Nat → Bool) : Bool :=
  allBelow 4096 (nodeP G D r k P)

@[expose] noncomputable def inOmK (n : Nat) : Bool :=
  o378K n && !f0K n 3 && !f0K n 192 && !Nat.beq n 3 && !Nat.beq n 192 && !Nat.beq n 195

end CFSG.KC.IF4W

end
