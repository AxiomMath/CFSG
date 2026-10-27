module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.CB

open CFSG.KC.Enum

@[expose] noncomputable def lexLt (a b c d : Nat) : Bool :=
  bIf(Nat.blt a c, true, bAnd(Nat.beq a c, Nat.blt b d))

@[expose] noncomputable def cbHead (n m root : Nat) (PTS PAR LAB : Nat → Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) m, bAnd(Nat.ble m n, bAnd(Nat.beq (PTS (nat_lit 0)) root,
    bAnd(Nat.beq (PAR (nat_lit 0)) (nat_lit 0), Nat.beq (LAB (nat_lit 0)) (nat_lit 0)))))

@[expose] noncomputable def cbPt (n m r : Nat) (STEP : Nat → Nat → Nat) (PTS POS PAR LAB : Nat → Nat)
    (k : Nat) : Bool :=
  strictB (PTS k) fun x => strictB (PAR k) fun p => strictB (LAB k) fun l =>
  bAnd(Nat.blt x n, bAnd(Nat.beq (POS x) k,
  bAnd(bIf(Nat.beq k (nat_lit 0), true,
      bAnd(Nat.blt p k, bAnd(Nat.blt l r, Nat.beq (STEP l (PTS p)) x))),
  bAnd(bIf(Nat.beq k (nat_lit 0), true, bIf(Nat.blt (Nat.succ k) m,
      lexLt p l (PAR (Nat.succ k)) (LAB (Nat.succ k)), true)),
    allN r fun j => strictB (STEP j x) fun y => strictB (POS y) fun kk =>
      bAnd(Nat.blt y n, bAnd(Nat.blt kk m, bIf(Nat.beq kk (nat_lit 0), true,
        Bool.not (lexLt k j (PAR kk) (LAB kk)))))))))

@[expose] noncomputable def cbPos (n m : Nat) (PTS POS : Nat → Nat) (z : Nat) : Bool :=
  strictB (POS z) fun q => bIf(Nat.beq q n, true, bAnd(Nat.blt q m, Nat.beq (PTS q) z))

@[expose] noncomputable def cbPtRange (n m r : Nat) (STEP : Nat → Nat → Nat) (PTS POS PAR LAB : Nat → Nat)
    (lo cnt : Nat) : Bool :=
  allBlk lo (fun k => bIf(Nat.blt k m, cbPt n m r STEP PTS POS PAR LAB k, true)) cnt

@[expose] noncomputable def cbPosRange (n m : Nat) (PTS POS : Nat → Nat) (lo cnt : Nat) : Bool :=
  allBlk lo (fun z => bIf(Nat.blt z n, cbPos n m PTS POS z, true)) cnt

end CFSG.KS.CB

end
