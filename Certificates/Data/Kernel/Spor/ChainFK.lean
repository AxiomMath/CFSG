module

public import Certificates.Data.Kernel.Spor.ChainK

public section

namespace CFSG.KS.CH

open CFSG.KC.Enum CFSG.KS.CB

@[expose] noncomputable def siftFull3 (n : Nat) (POS PAR LAB : Nat → Nat → Nat) (Mr : Nat → Nat)
    (INV : Nat → Nat → Nat → Nat) (B G : Nat → Nat) : Bool :=
  strictB (POS (nat_lit 0) (G (B (nat_lit 0)))) fun k0 =>
  strictB (POS (nat_lit 1)
    (trInvK (PAR (nat_lit 0)) (LAB (nat_lit 0)) (INV (nat_lit 0)) (Mr (nat_lit 0)) k0
      (G (B (nat_lit 1))))) fun k1 =>
  strictB (POS (nat_lit 2)
    (trInvK (PAR (nat_lit 1)) (LAB (nat_lit 1)) (INV (nat_lit 1)) (Mr (nat_lit 1)) k1
      (trInvK (PAR (nat_lit 0)) (LAB (nat_lit 0)) (INV (nat_lit 0)) (Mr (nat_lit 0)) k0
        (G (B (nat_lit 2)))))) fun k2 =>
  bAnd(Nat.blt k0 (Mr (nat_lit 0)), bAnd(Nat.blt k1 (Mr (nat_lit 1)),
    bAnd(Nat.blt k2 (Mr (nat_lit 2)), allN n fun y =>
      Nat.beq (trInvK (PAR (nat_lit 2)) (LAB (nat_lit 2)) (INV (nat_lit 2)) (Mr (nat_lit 2)) k2
        (trInvK (PAR (nat_lit 1)) (LAB (nat_lit 1)) (INV (nat_lit 1)) (Mr (nat_lit 1)) k1
          (trInvK (PAR (nat_lit 0)) (LAB (nat_lit 0)) (INV (nat_lit 0)) (Mr (nat_lit 0)) k0
            (G y)))) y)))

end CFSG.KS.CH

end
