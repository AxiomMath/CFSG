module

public import Certificates.Data.Kernel.D43.Tree

public section

namespace CFSG.KC.D43

open CFSG.KC.Enum

@[expose] noncomputable def dInv (d : Nat) : Nat :=
  nIf(Nat.blt (nat_lit 8) d, Nat.sub d (nat_lit 8), Nat.add d (nat_lit 8))

@[expose] noncomputable def wInvF : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih w acc => nIf(Nat.beq w (nat_lit 0), acc,
      strictN (Nat.add (Nat.shiftLeft acc (nat_lit 5)) (dInv (Nat.land w (nat_lit 31)))) fun a =>
        ih (Nat.shiftRight w (nat_lit 5)) a))

@[expose] noncomputable def wInv (w : Nat) : Nat := wInvF (nat_lit 24) w (nat_lit 0)

@[expose] noncomputable def letAp (F W : Nat → Nat) (d p : Nat) : Nat :=
  strictN (Nat.sub d (nat_lit 1)) fun e => strictN (Nat.shiftRight e (nat_lit 1)) fun j =>
    nIf(Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 0), lAp F W j p,
      wAp F (nat_lit 24) (wInv (W j)) p)

@[expose] noncomputable def evRF (F W : Nat → Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih w p => nIf(Nat.beq w (nat_lit 0), p,
      strictN (letAp F W (Nat.land w (nat_lit 63)) p) fun q => ih (Nat.shiftRight w (nat_lit 6)) q))

@[expose] noncomputable def evR (F W : Nat → Nat) (r p : Nat) : Nat := evRF F W (nat_lit 40) r p

@[expose] noncomputable def relChk (F W : Nat → Nat) (B r : Nat) : Bool :=
  bAnd(Nat.blt r (Nat.shiftLeft (nat_lit 1) (nat_lit 240)),
    allBlk (nat_lit 0) (fun u => strictB (bAt B u) fun b => Nat.beq (evR F W r b) b) (nat_lit 8))

@[expose] noncomputable def brelChunk (F W : Nat → Nat) (B : Nat) (R : Nat → Nat) (n c : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 16) c)
    (fun i => bIf(Nat.blt i n, relChk F W B (R i), true)) (nat_lit 16)

@[expose] noncomputable def key8F (F W : Nat → Nat) (B r : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun u acc => strictN acc fun a =>
      Nat.lor a (Nat.shiftLeft (evR F W r (bAt B u)) (Nat.mul (nat_lit 16) u)))

@[expose] noncomputable def key8 (F W : Nat → Nat) (B r : Nat) : Nat := key8F F W B r (nat_lit 8)

@[expose] noncomputable def valid8 (F W : Nat → Nat) (B r : Nat) : Bool :=
  bAnd(Nat.blt r (Nat.shiftLeft (nat_lit 1) (nat_lit 240)),
    allBlk (nat_lit 0) (fun u => Nat.blt (evR F W r (bAt B u)) (nat_lit 26572)) (nat_lit 8))

@[expose] noncomputable def bkeyChunk (F W : Nat → Nat) (B : Nat) (KW KK : Nat → Nat) (n c : Nat) :
    Bool :=
  allBlk (Nat.mul (nat_lit 13) c)
    (fun i => bIf(Nat.blt i n,
      bAnd(valid8 F W B (KW i), Nat.beq (key8 F W B (KW i)) (KK i)), true)) (nat_lit 13)

@[expose] noncomputable def distinctAll (KK : Nat → Nat) (n : Nat) : Bool :=
  allBlk (nat_lit 0) (fun i => strictB (KK i) fun a => allBlk (Nat.add i (nat_lit 1))
    (fun j => bIf(Nat.blt j n, bIf(Nat.beq a (KK j), false, true), true)) n) n

@[expose] noncomputable def neqChunk (F W : Nat → Nat) (B : Nat) (X Y : Nat → Nat) (n c : Nat) :
    Bool :=
  allBlk (Nat.mul (nat_lit 17) c)
    (fun i => bIf(Nat.blt i n, bAnd(valid8 F W B (X i), bAnd(valid8 F W B (Y i),
      bIf(Nat.beq (key8 F W B (X i)) (key8 F W B (Y i)), false, true))), true)) (nat_lit 17)

end CFSG.KC.D43
