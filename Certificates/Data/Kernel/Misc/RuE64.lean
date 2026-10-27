module

public import Certificates.Data.Kernel.Spor.Raw
public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.RuE64

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KLie.CT (bit anyN sumN popc)

@[expose, reducible] noncomputable def ap (p x : Nat) : Nat := pg (nat_lit 12) (mask (nat_lit 12)) p x

@[expose] noncomputable def trK (LR TR : Nat → Nat) (i k : Nat) : Nat :=
  TR (roff (nat_lit 4060) (nat_lit 4060 * nat_lit 12) (LR i) + k)

@[expose] noncomputable def evK (LR TR : Nat → Nat) (c x : Nat) : Nat :=
  ap (trK LR TR 0 (c / 8)) (ap (trK LR TR 1 (c % 8)) x)

@[expose] noncomputable def invK (LR TR : Nat → Nat) (c : Nat) : Bool :=
  bAnd(Nat.beq (evK LR TR c (evK LR TR c 1)) 1, bAnd(Nat.beq (evK LR TR c (evK LR TR c 0)) 0,
    bIf(bAnd(Nat.beq (evK LR TR c 1) 1, Nat.beq (evK LR TR c 0) 0), false, true)))

@[expose] noncomputable def comK (LR TR : Nat → Nat) (c d : Nat) : Bool :=
  bAnd(Nat.beq (evK LR TR c (evK LR TR d 1)) (evK LR TR d (evK LR TR c 1)),
    Nat.beq (evK LR TR c (evK LR TR d 0)) (evK LR TR d (evK LR TR c 0)))

@[expose] noncomputable def inWK (LR TR UB : Nat → Nat) (c : Nat) : Bool :=
  anyN 64 fun e => bAnd(Nat.beq (evK LR TR c 1) (UB (2 * e)), Nat.beq (evK LR TR c 0) (UB (2 * e + 1)))

@[expose] noncomputable def keepK (N : Nat) (R : Nat → Nat) (i j : Nat) : Bool :=
  bAnd(bIf(Nat.beq i j, false, true), bAnd(bit (R i) j, Nat.ble 63 (popc N (Nat.land (R i) (R j)))))

@[expose] noncomputable def multiK (W : Nat → Nat) (i : Nat) : Bool :=
  Nat.ble 2 (sumN 4 fun r => Bool.rec (motive := fun _ => Nat) 0 1 (bit (W r) i))

@[expose] noncomputable def localK (N : Nat) (K D W : Nat → Nat) (i : Nat) : Bool :=
  bIf(Nat.blt (D i) 62, true, bIf(multiK W i, true, anyN 4 fun r => bAnd(bit (W r) i,
    allN N fun j => bIf(bit (K i) j, bIf(Nat.blt (D j) 62, true, bit (W r) j), true))))

@[expose] noncomputable def e64K (N : Nat) (K D W : Nat → Nat) : Bool :=
  bAnd(allN N (localK N K D W),
    Nat.ble (sumN N fun i => Bool.rec (motive := fun _ => Nat) 0 1 (multiK W i)) 62)

end CFSG.KC.RuE64

end
