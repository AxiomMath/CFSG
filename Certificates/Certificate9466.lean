module

import Certificates.Kernel.J3Coset.Model
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace Certificates

theorem certificate9466 : ∀ (J : Type) [Group J] [Finite J],
    Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) → IsSimpleGroup J →
      Nat.card J = 50232960 → ∃ (T : Sylow 3 J) (φ : MulAut J),
        (∀ x ∈ (T : Subgroup J), φ x ∈ (T : Subgroup J)) ∧
        φ ∉ (MulAut.conj : J →* MulAut J).range ∧
        (∀ z ∈ CFSG.Quasithin.centerOf (T : Subgroup J), z ≠ 1 →
          Subgroup.centralizer {z} ≤ Subgroup.normalizer ((T : Subgroup J) : Set J) →
          Subgroup.centralizer {z} ≤ T) ∧
        (∀ x ∈ Subgroup.normalizer ((T : Subgroup J) : Set J), (MulAut.conj x * φ) ^ 2 = 1 →
          ∀ E : Subgroup J, E ≤ T → IsMulCommutative E → (∀ y ∈ E, y ^ 3 = 1) →
            Nat.card E = 9 → ∃ y ∈ E, (MulAut.conj x * φ) y ≠ y) :=
  CertificateChecks.KernelJ3C.fact9466

end Certificates
