module

public import Certificates.Data.Kernel.Spor.ChainK
public import CFSG.Certificates.Kernel.Spor.CBComm

public section

namespace CFSG.KS.CH

open CFSG.KC.Enum CFSG.KS.CB

@[expose] noncomputable def schImg (STEP INV : Nat → Nat → Nat → Nat) (PAR LAB : Nat → Nat → Nat)
    (Mr : Nat → Nat) (i h j k p : Nat) : Nat :=
  trInvK (PAR i) (LAB i) (INV i) (Mr i) k (STEP i j (trK (STEP i) (PAR i) (LAB i) (Mr i) h p))

@[expose] noncomputable def schK (STEP INV : Nat → Nat → Nat → Nat) (PTS POS PAR LAB : Nat → Nat → Nat)
    (Mr B : Nat → Nat) (i h j : Nat) : Bool :=
  strictB (POS i (STEP i j (PTS i h))) fun k =>
  bAnd(Nat.blt k (Mr i),
    bIf(Nat.beq i (nat_lit 2), true,
      bIf(Nat.beq i (nat_lit 1),
        Nat.blt (POS (nat_lit 2) (schImg STEP INV PAR LAB Mr i h j k (B (nat_lit 2))))
          (Mr (nat_lit 2)),
        strictB (POS (nat_lit 1) (schImg STEP INV PAR LAB Mr i h j k (B (nat_lit 1)))) fun k1 =>
          bAnd(Nat.blt k1 (Mr (nat_lit 1)),
            Nat.blt (POS (nat_lit 2) (trInvK (PAR (nat_lit 1)) (LAB (nat_lit 1)) (INV (nat_lit 1))
              (Mr (nat_lit 1)) k1 (schImg STEP INV PAR LAB Mr i h j k (B (nat_lit 2)))))
              (Mr (nat_lit 2))))))

@[expose] noncomputable def treePt (n r : Nat) (STEP : Nat → Nat → Nat) (PTS POS PAR LAB : Nat → Nat)
    (root k : Nat) : Bool :=
  strictB (PTS k) fun x => bAnd(Nat.blt x n, bAnd(Nat.beq (POS x) k,
    bIf(Nat.beq k (nat_lit 0), Nat.beq x root,
      bAnd(Nat.blt (PAR k) k, bAnd(Nat.blt (LAB k) r, Nat.beq (STEP (LAB k) (PTS (PAR k))) x)))))

end CFSG.KS.CH

end
