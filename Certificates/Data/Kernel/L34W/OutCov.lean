module

public import Certificates.Data.Kernel.L34W.ModK
public import Certificates.Data.Kernel.L34Scan
public import Certificates.Data.Kernel.L34Scan2

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34K CFSG.KC.L34Scan CFSG.KC.L34Scan2
open CFSG.KLie.CT (notB)

@[expose] noncomputable def pc (x y : Nat) : Nat := pcomp (nat_lit 42) (nat_lit 6) (mask 6) x y

@[expose] noncomputable def orK (a b : Bool) : Bool := bIf(a, true, b)

@[expose] noncomputable def tabAt (R j : Nat) : Nat := pg (nat_lit 252) (mask 252) R j

@[expose] noncomputable def invK (A : Nat → Nat) (k₁ k₂ m i : Nat) : Bool :=
  strictB (ent A i (nat_lit 64)) fun p => strictB (ent A i (nat_lit 65)) fun q =>
    bitC m (Nat.add
      (Nat.mul (nat_lit 4) (Nat.mod (Nat.add (Nat.mul k₁ (Nat.div (Nat.mod p (nat_lit 48)) (nat_lit 12)))
        (Nat.mul k₂ (Nat.div (Nat.mod q (nat_lit 48)) (nat_lit 12)))) (nat_lit 4)))
      (Nat.mod (Nat.add (Nat.mul k₁ (Nat.div (Nat.mod p (nat_lit 12)) (nat_lit 3)))
        (Nat.mul k₂ (Nat.div (Nat.mod q (nat_lit 12)) (nat_lit 3)))) (nat_lit 4)))

@[expose] noncomputable def inLK (Y A : Nat → Nat) (k₁ k₂ m P n : Nat) : Bool :=
  bAnd(invK A k₁ k₂ m (Nat.div n (nat_lit 64)), commPt (nat_lit 42) (nat_lit 6) (Y n) P)

@[expose] noncomputable def lOK (Y A : Nat → Nat) (k₁ k₂ m P LT nL : Nat) : Bool :=
  bAnd(allN (nat_lit 2304) fun n =>
      bEq (inLK Y A k₁ k₂ m P n) (memL nL (fun k => pg (nat_lit 12) (mask 12) LT k) n),
    allN nL fun k => Nat.blt (pg (nat_lit 12) (mask 12) LT k) (nat_lit 2304))

@[expose] noncomputable def is2K (x : Nat) : Bool :=
  Nat.beq (pow2K (nat_lit 42) (nat_lit 6) (nat_lit 8) x) (pidn (nat_lit 42) (nat_lit 6))

@[expose] noncomputable def two1 (x s : Nat) : Bool := bAnd(is2K (pc x s), is2K (pc s x))

@[expose] noncomputable def twoK (x x₁ P FT nF : Nat) : Bool :=
  bAnd(is2K x, bAnd(two1 x x₁, bAnd(two1 x P, allN nF fun j => two1 x (tabAt FT j))))

@[expose] noncomputable def c3C (x P FT nF : Nat) : Bool :=
  bAnd(commPt (nat_lit 42) (nat_lit 6) x P, bAnd(invPt (nat_lit 42) (nat_lit 6) x,
    allN nF fun j => commPt (nat_lit 42) (nat_lit 6) x (tabAt FT j)))

@[expose] noncomputable def wit3 (ST : Nat → Nat) (P n y r : Nat) : Bool :=
  bAnd(Nat.beq (Nat.mod r (nat_lit 4096)) n, bAnd(Nat.blt (Nat.div r (nat_lit 8192)) (nat_lit 20160),
    Nat.beq (ST (Nat.div r (nat_lit 8192)))
      (nIf(Nat.beq (Nat.mod (Nat.div r (nat_lit 4096)) (nat_lit 2)) (nat_lit 0), y, pc y P))))

@[expose] noncomputable def c3K (Y ST : Nat → Nat) (P FT nF S3 nS : Nat) : Bool :=
  allN (nat_lit 2304) fun n => strictB (Y n) fun y =>
    bIf(c3C y P FT nF,
      CFSG.KLie.CT.notB (allN nS fun e => CFSG.KLie.CT.notB (wit3 ST P n y (pg (nat_lit 32) (mask 32) S3 e))), true)

@[expose] noncomputable def invW (T : Nat → Nat) (m w : Nat) : Bool :=
  bAnd(Nat.blt w (nat_lit 1024), bAnd(eqC m (mulC T w w) (nat_lit 0),
    bNot (Nat.beq (Nat.div w (nat_lit 16)) (nat_lit 0))))

@[expose] noncomputable def fixW (T A : Nat → Nat) (m n w : Nat) : Bool :=
  eqC m (betaC T A (Nat.mod n (nat_lit 64)) (Nat.div n (nat_lit 64)) w) w

@[expose] noncomputable def c4AK (Y T A E : Nat → Nat) (cnt m LT nL wA : Nat) : Bool :=
  bAnd(invW T m wA, allN nL fun k => strictB (pg (nat_lit 12) (mask 12) LT k) fun n =>
    orK (bNot (memL cnt E (Y n))) (fixW T A m n wA))

@[expose] noncomputable def c4BK (Y T A E : Nat → Nat) (cnt m P FT nF LT nL WB : Nat) : Bool :=
  allN nL fun k₁ => strictB (pg (nat_lit 12) (mask 12) LT k₁) fun n₁ => strictB (Y n₁) fun x₁ =>
    orK (memL cnt E x₁) (orK (bNot (is2K x₁)) (strictB (pg (nat_lit 10) (mask 10) WB k₁) fun w =>
      bAnd(invW T m w, allN nL fun k => strictB (pg (nat_lit 12) (mask 12) LT k) fun n =>
        orK (fixW T A m n w) (bNot (twoK (Y n) x₁ P FT nF)))))

@[expose] noncomputable def invsK (T A : Nat → Nat) (m i : Nat) : Bool :=
  bAnd(eqC m (betaC T A (nat_lit 0) i (nat_lit 4)) (nat_lit 12),
    eqC m (betaC T A (nat_lit 0) i (nat_lit 1)) (nat_lit 3))

@[expose] noncomputable def c5K (T A : Nat → Nat) (m i V : Nat) : Bool :=
  orK (bNot (invsK T A m i)) (allN (nat_lit 1024) fun x =>
    bIf(bAnd(eqC m (mulC T x x) (nat_lit 0), eqC m (betaC T A (nat_lit 0) i x) x),
      strictB (pg (nat_lit 10) (mask 10) V x) fun v =>
        eqC m v (mulC T (betaC T A (nat_lit 0) i v) x),
      true))

@[expose] noncomputable def fixOK (T A : Nat → Nat) (m i FK nF : Nat) : Bool :=
  bAnd(allN (nat_lit 64) fun k =>
      bEq (memL nF (fun j => pg (nat_lit 6) (mask 6) FK j) k)
        (CFSG.KLie.CT.notB (allN (nat_lit 16) fun ab => strictB (Nat.add (Nat.mul (nat_lit 16) k) ab) fun x =>
          CFSG.KLie.CT.notB (eqC m (betaC T A (nat_lit 0) i x) x))),
    allN nF fun j => bAnd(Nat.blt (pg (nat_lit 6) (mask 6) FK j) (nat_lit 64),
      bIf(Nat.blt (Nat.succ j) nF,
        Nat.blt (pg (nat_lit 6) (mask 6) FK j) (pg (nat_lit 6) (mask 6) FK (Nat.succ j)), true)))

@[expose] noncomputable def genOK (G EG : Nat → Nat) (FK FT nF P k : Nat) : Bool :=
  bAnd(allN nF fun j => bAnd(Nat.beq (tabAt FT j) (tgK G (pg (nat_lit 6) (mask 6) FK j)),
      Nat.beq (EG j) (tabAt FT j)),
    bAnd(Nat.beq (EG nF) P, Nat.beq k (Nat.succ nF)))

@[expose] noncomputable def hf (h f : Nat) : Nat := pg (nat_lit 16) (mask 16) h f

@[expose] noncomputable def invOKK (T : Nat → Nat) : Bool :=
  allN (nat_lit 64) fun t => Nat.beq (Nat.div (ent T t (invIdxC T t)) (nat_lit 48)) (nat_lit 0)

@[expose] noncomputable def matchOK (Y RP : Nat → Nat) : Bool :=
  allN (nat_lit 3) fun r => strictB (RP (Nat.succ r)) fun p => allN (nat_lit 2304) fun n =>
    bEq (Nat.beq (Y n) p) (Nat.beq n (Nat.mul (nat_lit 64) (Nat.succ r)))

@[expose] noncomputable def kapOK (A K : Nat → Nat) : Bool :=
  allN (nat_lit 6) fun j => strictB (K j) fun h => allN (nat_lit 3) fun r =>
    bEq (invK A (hf h 0) (hf h 1) (hf h 2) (Nat.succ r)) (hasBit (hf h 3) r)

@[expose] noncomputable def caseK (Y ST T A G EG E : Nat → Nat) (h FK FT LT S3 WB V cnt k : Nat) :
    Bool :=
  strictB (Y (hf h 0)) fun P =>
  bAnd(bAnd(fixOK T A (hf h 3) (Nat.div (hf h 0) (nat_lit 64)) FK (hf h 4),
      genOK G EG FK FT (hf h 4) P k),
    bAnd(bAnd(lOK Y A (hf h 1) (hf h 2) (hf h 3) P LT (hf h 5),
        c3K Y ST P FT (hf h 4) S3 (hf h 7)),
      bAnd(bAnd(c4AK Y T A E cnt (hf h 3) LT (hf h 5) (hf h 6),
          c4BK Y T A E cnt (hf h 3) P FT (hf h 4) LT (hf h 5) WB),
        c5K T A (hf h 3) (Nat.div (hf h 0) (nat_lit 64)) V)))

end CFSG.KC.L34W

end
