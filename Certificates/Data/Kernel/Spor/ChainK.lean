module

public import Certificates.Data.Kernel.Spor.CBfsK
public import CFSG.Certificates.Kernel.Spor.CBTrInv

public section

namespace CFSG.KS.CH

open CFSG.KC.Enum CFSG.KS.CB

@[expose] noncomputable def stepX (F FI : Nat → Nat → Nat) (IDX : Nat → Nat) (len j x : Nat) : Nat :=
  nIf(Nat.blt j len, F (IDX j) x, FI (IDX (Nat.sub j len)) x)

@[expose] noncomputable def invX (F FI : Nat → Nat → Nat) (IDX : Nat → Nat) (len j x : Nat) : Nat :=
  nIf(Nat.blt j len, FI (IDX j) x, F (IDX (Nat.sub j len)) x)

@[expose] noncomputable def fixesK (F : Nat → Nat → Nat) (B : Nat → Nat) (i j : Nat) : Bool :=
  allN i fun k => Nat.beq (F j (B k)) (B k)

@[expose] noncomputable def cntB (s : Nat) (q : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j ih => Nat.add (nIf(q j, nat_lit 1, nat_lit 0)) ih) s

@[expose] noncomputable def idxOK (F : Nat → Nat → Nat) (s : Nat) (B : Nat → Nat) (i : Nat)
    (IDX : Nat → Nat) (len : Nat) : Bool :=
  bAnd(allN len fun t => bAnd(Nat.blt (IDX t) s, bAnd(fixesK F B i (IDX t),
      bIf(Nat.blt (Nat.succ t) len, Nat.blt (IDX t) (IDX (Nat.succ t)), true))),
    Nat.beq (cntB s (fixesK F B i)) len)

@[expose] noncomputable def sift3 (POS PAR LAB : Nat → Nat → Nat) (Mr : Nat → Nat)
    (INV : Nat → Nat → Nat → Nat) (g0 g1 g2 : Nat) : Bool :=
  strictB (POS (nat_lit 0) g0) fun k0 =>
  strictB (trInvK (PAR (nat_lit 0)) (LAB (nat_lit 0)) (INV (nat_lit 0)) (Mr (nat_lit 0)) k0 g1)
    fun y1 =>
  strictB (trInvK (PAR (nat_lit 0)) (LAB (nat_lit 0)) (INV (nat_lit 0)) (Mr (nat_lit 0)) k0 g2)
    fun y2 =>
  strictB (POS (nat_lit 1) y1) fun k1 =>
  strictB (trInvK (PAR (nat_lit 1)) (LAB (nat_lit 1)) (INV (nat_lit 1)) (Mr (nat_lit 1)) k1 y2)
    fun y2' =>
  bAnd(Nat.blt k0 (Mr (nat_lit 0)), bAnd(Nat.blt k1 (Mr (nat_lit 1)),
    Nat.blt (POS (nat_lit 2) y2') (Mr (nat_lit 2))))

end CFSG.KS.CH

end
