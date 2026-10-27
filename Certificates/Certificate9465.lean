module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3CoverGroup
import Certificates.Kernel.J3Coset.Model
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace Certificates

theorem certificate9465 : ∀ (J : Type) [Group J] [Finite J],
    Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) → IsSimpleGroup J →
      Nat.card J = 50232960 →
        (∃ x d₁ d₂ g u : J, CFSG.AGLEmbedding.KFactProofs.J3Cover.CoverData x d₁ d₂ g u) ∧
        ∀ T : Sylow 3 J, ∀ K : Subgroup J, (T : Subgroup J) ≤ K →
          K ≤ Subgroup.normalizer ((T : Subgroup J) : Set J) ∨ K = ⊤ :=
  CertificateChecks.KernelJ3C.fact9465

end Certificates
