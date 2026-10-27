module

public import Certificates.Data.Kernel.L34W.Model
public import Certificates.Data.Kernel.L34W.OutCov

public section

namespace CFSG.KC.L34FU

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34W CFSG.KC.L34Scan2

@[expose] noncomputable def ex8K (x : Nat) : Bool :=
  strictB (pc x x) fun x2 => strictB (pc x2 x2) fun x4 =>
    Nat.beq (pc x4 x4) (pidn (nat_lit 42) (nat_lit 6))

@[expose] noncomputable def expK (N : Nat) (T : Nat → Nat) : Bool := allN N fun q => ex8K (T q)

@[expose] noncomputable def candK (R2 : Nat) (OT : Nat → Nat) (y : Nat) : Bool :=
  bAnd(Nat.beq (pc y R2) (pc R2 y),
    bAnd(Nat.beq (pc y y) (pidn (nat_lit 42) (nat_lit 6)), memL (nat_lit 280) OT y))

@[expose] noncomputable def witK (T A : Nat → Nat) (t i x : Nat) : Bool :=
  bAnd(Nat.blt x (nat_lit 1024), bAnd(Nat.beq (betaRepC A (nat_lit 1) x) x,
    strictB (mulC T x (betaC T A t i x)) fun u => strictB (mulC T u u) fun u2 =>
      Nat.beq (mulC T u2 u2) (nat_lit 8)))

@[expose] noncomputable def sixK (T A Y OT W : Nat → Nat) (R2 : Nat) : Bool :=
  allN (nat_lit 36) fun i => strictB (W i) fun row => allN (nat_lit 64) fun t =>
    bIf(candK R2 OT (Y (Nat.add (Nat.mul (nat_lit 64) i) t)),
      witK T A t i (pg (nat_lit 11) (mask 11) row t), true)

end CFSG.KC.L34FU

end
