module

public import Certificates.Data.Kernel.J2Enum

public section

namespace CFSG.KC.J2Cent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Child3

@[expose] noncomputable def commB (w m E : Nat) (x : Nat → Nat) (p0 p1 p2 q0 q1 q2 : Nat) : Bool :=
  bAnd(Nat.beq (x q0) (pg w m E (x p0)),
    bAnd(Nat.beq (x q1) (pg w m E (x p1)), Nat.beq (x q2) (pg w m E (x p2))))

@[expose] noncomputable def blkCent (n w : Nat) (LR TR : Nat → Nat) (BP E₁ E₂ a : Nat) : Nat :=
  strictN (pg w (mask w) BP 0) (fun p0 => strictN (pg w (mask w) BP 1) (fun p1 =>
  strictN (pg w (mask w) BP 2) (fun p2 =>
  strictN (pg w (mask w) E₁ p0) (fun q0 => strictN (pg w (mask w) E₁ p1) (fun q1 =>
  strictN (pg w (mask w) E₁ p2) (fun q2 =>
  strictN (pg w (mask w) E₂ p0) (fun r0 => strictN (pg w (mask w) E₂ p1) (fun r1 =>
  strictN (pg w (mask w) E₂ p2) (fun r2 =>
  strictN (LR 0) (fun L0 => strictN (LR 1) (fun L1 => strictN (LR 2) (fun L2 =>
  strictN (TR (Nat.add (roff n (Nat.mul n w) L0) a)) (fun g1 =>
  sumF (rcnt L1) (fun b => strictN (pcomp n w (mask w) g1 (TR (Nat.add (roff n (Nat.mul n w) L1) b)))
    (fun g2 => sumF (rcnt L2) (fun c => strictN (TR (Nat.add (roff n (Nat.mul n w) L2) c))
      (fun t => Nat.add
        (nIf(commB w (mask w) E₁ (fun p => pg w (mask w) g2 (pg w (mask w) t p)) p0 p1 p2 q0 q1 q2,
          nat_lit 1, nat_lit 0))
        (nIf(commB w (mask w) E₂ (fun p => pg w (mask w) g2 (pg w (mask w) t p)) p0 p1 p2 r0 r1 r2,
          Nat.shiftLeft 1 20, nat_lit 0)))))))))))))))))))

@[expose] noncomputable def blkKey (n w : Nat) (LR TR : Nat → Nat) (BP a : Nat) : Nat :=
  pg w (mask w) (TR (Nat.add (roff n (Nat.mul n w) (LR 0)) a)) (pg w (mask w) BP 0)

end CFSG.KC.J2Cent

end
