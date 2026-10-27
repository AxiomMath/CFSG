module

public import Certificates.Data.Kernel.E27Lie.Defs

public section

namespace CFSG.KC.Fi22Rank

open CFSG.KC.Ord CFSG.KC.Enum

@[expose] noncomputable def distinct4 (a b c d : Nat) : Bool :=
  bAnd(notB (Nat.beq a b), bAnd(notB (Nat.beq a c), bAnd(notB (Nat.beq a d),
    bAnd(notB (Nat.beq b c), bAnd(notB (Nat.beq b d), notB (Nat.beq c d))))))

@[expose] noncomputable def smallC (mm : Nat → Nat → Nat) (key REP SM : Nat → Nat)
    (H Y : Nat → Nat → Nat) (n c : Nat) : Bool :=
  bIf(Nat.beq (SM c) (nat_lit 1), strictB (REP c) fun r =>
    bAnd(Nat.blt r n, bAnd(distinct4 r (Y c (nat_lit 0)) (Y c (nat_lit 1)) (Y c (nat_lit 2)),
      allN (nat_lit 3) fun t => strictB (H c t) fun h => strictB (Y c t) fun y =>
        bAnd(Nat.blt h n, bAnd(Nat.blt y n, Nat.beq (mm (key h) (key r)) (mm (key y) (key h)))))),
    true)

@[expose] noncomputable def bigC (CI SM BL BP : Nat → Nat) (nb a : Nat) : Bool :=
  bIf(bAnd(notB (Nat.beq a (nat_lit 0)), Nat.beq (SM (CI a)) (nat_lit 1)), true,
    strictB (BP a) fun p => bAnd(Nat.blt p nb, Nat.beq (BL p) a))

end CFSG.KC.Fi22Rank

end
