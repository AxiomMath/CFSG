module

public import Certificates.Data.Kernel.Co1Three.Slp

public section

namespace CFSG.KC.Co1Cl

open CFSG.KC.Enum CFSG.KC.Co1F2

@[expose] noncomputable def fixFreeK (R B : List Nat) : Bool :=
  allN (Nat.sub (Nat.pow (nat_lit 3) (lenL B)) (nat_lit 1)) fun a =>
    strictB (actK (nat_lit 3) (nat_lit 6) B (Nat.succ a) (nat_lit 0)) fun c =>
      bIf(Nat.beq (actK (nat_lit 3) (nat_lit 6) R c (nat_lit 0)) c, false, true)

end CFSG.KC.Co1Cl

end
