module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3SylowGroup
import Certificates.Kernel.J3Coset.Model

public section

namespace Certificates

theorem certificate9435 : ∀ (J : Type) [Group J] [Finite J],
    Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) → IsSimpleGroup J →
      Nat.card J = 50232960 → ∀ T : Sylow 3 J, ∃ (H : Subgroup J) (t₁ t₂ s : J)
        (Z : Fin 9 → J) (w₁ w₂ : List Bool), Subgroup.closure ({t₁, t₂} : Set J) = T ∧
          IsCoatom H ∧ CFSG.AGLEmbedding.KFactProofs.J3Sylow.LocalData H t₁ t₂ s Z w₁ w₂ :=
  CertificateChecks.KernelJ3C.fact9435

end Certificates
