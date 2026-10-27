module

public import Certificates.Certificate709548
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.StandardType.FrameRoute

theorem frameE78_facts {n : ℕ} (hn : n = 7 ∨ n = 8) :
    (∀ r ∈ feT n, ∀ t ∈ feT n, r = t ∨ r * t = t * r ∨ r * t * r = t * r * t) ∧
    ∀ x : FEVec n, x ≠ 0 →
      (∃ P Q : Set (FEMat n), P ∪ Q = feTx n x ∧ Disjoint P Q ∧ P.Nonempty ∧ Q.Nonempty ∧
          (∀ r ∈ P, ∀ t ∈ P, t * r * t ∈ P) ∧ (∀ r ∈ Q, ∀ t ∈ Q, t * r * t ∈ Q) ∧
          ∀ r ∈ P, ∀ t ∈ Q, r * t = t * r) ∨
      ∃ d : ℕ, (∀ r ∈ feTx n x, Set.ncard {t | t ∈ feTx n x ∧ r * t ≠ t * r} = d) ∧
        ((n = 7 ∧ ((Set.ncard (feTx n x) = 21 ∧ d = 10) ∨ (Set.ncard (feTx n x) = 30 ∧ d = 16) ∨
            (Set.ncard (feTx n x) = 36 ∧ d = 20))) ∨
         (n = 8 ∧ ((Set.ncard (feTx n x) = 36 ∧ d = 14) ∨ (Set.ncard (feTx n x) = 42 ∧ d = 20) ∨
            (Set.ncard (feTx n x) = 63 ∧ d = 32)))) :=
  Certificates.certificate709548 hn

end CFSG.StandardType.FrameRoute

end
