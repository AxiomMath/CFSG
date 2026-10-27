module

public import Certificates.Data.Kernel.L34W.ModK

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34K

@[expose] noncomputable def hjLab (T A : Nat → Nat) (g gi i x : Nat) : Bool :=
  bAnd(eqC (nat_lit 1285) (mulC T x x) (nat_lit 0), eqC (nat_lit 1285) (betaW T A g gi i x) x)

@[expose] noncomputable def hjOne (T A Y : Nat → Nat) (n : Nat) : Bool :=
  bIf(invPt (nat_lit 42) (nat_lit 6) (Y n),
    strictB (Nat.mul (nat_lit 16) (Nat.mod n (nat_lit 64))) fun g =>
    strictB (invC T g) fun gi => strictB (Nat.div n (nat_lit 64)) fun i =>
      bIf(eqC (nat_lit 1285) (betaW T A g gi i (nat_lit 1)) (nat_lit 1),
        bIf(hjLab T A g gi i (nat_lit 68), true,
          bIf(hjLab T A g gi i (nat_lit 133), true, hjLab T A g gi i (nat_lit 197))),
        true),
    true)

@[expose] noncomputable def hjK (T A Y : Nat → Nat) : Bool :=
  bAnd(bAnd(bNot (Nat.beq (Y (nat_lit 4)) (pidn (nat_lit 42) (nat_lit 6))),
      bAnd(bNot (Nat.beq (Y (nat_lit 8)) (pidn (nat_lit 42) (nat_lit 6))),
        bNot (Nat.beq (Y (nat_lit 12)) (pidn (nat_lit 42) (nat_lit 6))))),
    allN (nat_lit 2304) fun n => hjOne T A Y n)

end CFSG.KC.L34W

end
