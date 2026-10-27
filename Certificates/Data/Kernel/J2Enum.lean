module

public import Certificates.Data.Kernel.Child3

public section

namespace CFSG.KC.J2Enum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Child3

@[expose] noncomputable def itP (f : Nat → Nat) (k p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ q => strictN q f) k

@[expose] noncomputable def fix3 (w m BP : Nat) (f : Nat → Nat) (k : Nat) : Bool :=
  bAnd(Nat.beq (itP f k (pg w m BP 0)) (pg w m BP 0),
    bAnd(Nat.beq (itP f k (pg w m BP 1)) (pg w m BP 1), Nat.beq (itP f k (pg w m BP 2)) (pg w m BP 2)))

@[expose] noncomputable def ordB (w m BP : Nat) (f : Nat → Nat) (k : Nat) : Bool :=
  bAnd(fix3 w m BP f k, bIf(fix3 w m BP f 1, false, true))

@[expose] noncomputable def ord12B (w m BP : Nat) (f : Nat → Nat) : Bool :=
  bAnd(fix3 w m BP f 12, bAnd(bIf(fix3 w m BP f 6, false, true), bAnd(bIf(fix3 w m BP f 4, false, true),
    bAnd(bIf(fix3 w m BP f 3, false, true), bAnd(bIf(fix3 w m BP f 2, false, true),
      bIf(fix3 w m BP f 1, false, true))))))

@[expose] noncomputable def pairB (w m BP R : Nat) (y : Nat → Nat) : Bool :=
  bAnd(ordB w m BP (fun p => pg w m R (y p)) 7,
    ord12B w m BP (fun p => pg w m R (y (pg w m R (y (y p))))))

@[expose] noncomputable def contrib (w m BP R₁ R₂ : Nat) (x : Nat → Nat) : Nat :=
  Nat.add (nIf(ordB w m BP x 2, nat_lit 1, nat_lit 0))
    (nIf(ordB w m BP x 3, Nat.add (Nat.shiftLeft 1 20)
      (Nat.add (nIf(pairB w m BP R₁ x, Nat.shiftLeft 1 40, nat_lit 0))
        (nIf(pairB w m BP R₂ x, Nat.shiftLeft 1 60, nat_lit 0))), nat_lit 0))

@[expose] noncomputable def blkCnt (n w : Nat) (LR TR : Nat → Nat) (BP G₀ R₁ R₂ a : Nat) : Nat :=
  strictN (LR 0) (fun L0 => strictN (LR 1) (fun L1 => strictN (LR 2) (fun L2 =>
  strictN (pcomp n w (mask w) G₀ (TR (Nat.add (roff n (Nat.mul n w) L0) a))) (fun g1 =>
  sumF (rcnt L1) (fun b => strictN (pcomp n w (mask w) g1 (TR (Nat.add (roff n (Nat.mul n w) L1) b)))
    (fun g2 => sumF (rcnt L2) (fun c => strictN (TR (Nat.add (roff n (Nat.mul n w) L2) c))
      (fun t => contrib w (mask w) BP R₁ R₂ (fun p => pg w (mask w) g2 (pg w (mask w) t p))))))))))

@[expose] noncomputable def blkCntU (n w : Nat) (LR TR : Nat → Nat) (BP G₀ a : Nat) : Nat :=
  strictN (LR 0) (fun L0 => strictN (LR 1) (fun L1 => strictN (LR 2) (fun L2 =>
  strictN (pcomp n w (mask w) G₀ (TR (Nat.add (roff n (Nat.mul n w) L0) a))) (fun g1 =>
  sumF (rcnt L1) (fun b => strictN (pcomp n w (mask w) g1 (TR (Nat.add (roff n (Nat.mul n w) L1) b)))
    (fun g2 => sumF (rcnt L2) (fun c => strictN (TR (Nat.add (roff n (Nat.mul n w) L2) c))
      (fun t => nIf(fix3 w (mask w) BP (fun p => pg w (mask w) g2 (pg w (mask w) t p)) 2,
        nat_lit 1, nat_lit 0)))))))))

@[expose] noncomputable def fld20 (T k : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul 20 k)) (nat_lit 1048575)

end CFSG.KC.J2Enum

end
