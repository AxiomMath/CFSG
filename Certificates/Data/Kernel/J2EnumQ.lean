module

public import Certificates.Data.Kernel.J2Enum

public section

namespace CFSG.KC.J2Enum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Child3

@[expose] noncomputable def pairQ (w m BP R q r s : Nat) (y : Nat → Nat) : Bool :=
  bAnd(ordB w m BP (fun p => pg w m R (y p)) r,
    ordB w m BP (fun p => pg w m R (y (pg w m R (itP y (Nat.sub q 1) p)))) s)

@[expose] noncomputable def contribQ (w m BP R₁ R₂ q r s : Nat) (x : Nat → Nat) : Nat :=
  nIf(ordB w m BP x q, Nat.add (nIf(pairQ w m BP R₁ q r s x, nat_lit 1, nat_lit 0))
    (nIf(pairQ w m BP R₂ q r s x, Nat.shiftLeft 1 20, nat_lit 0)), nat_lit 0)

@[expose] noncomputable def blkCntQ (n w : Nat) (LR TR : Nat → Nat) (BP G₀ R₁ R₂ q r s a : Nat) :
    Nat :=
  strictN (LR 0) (fun L0 => strictN (LR 1) (fun L1 => strictN (LR 2) (fun L2 =>
  strictN (pcomp n w (mask w) G₀ (TR (Nat.add (roff n (Nat.mul n w) L0) a))) (fun g1 =>
  sumF (rcnt L1) (fun b => strictN (pcomp n w (mask w) g1 (TR (Nat.add (roff n (Nat.mul n w) L1) b)))
    (fun g2 => sumF (rcnt L2) (fun c => strictN (TR (Nat.add (roff n (Nat.mul n w) L2) c))
      (fun t => contribQ w (mask w) BP R₁ R₂ q r s
        (fun p => pg w (mask w) g2 (pg w (mask w) t p))))))))))

end CFSG.KC.J2Enum

end
