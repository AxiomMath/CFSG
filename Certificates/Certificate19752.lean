
module

public import CFSG.Open.LocalVocabulary
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.CoreD2K.M24.Glue

public section

namespace Certificates

theorem certificate19752 :
    ∃ (E : Subgroup ↥CFSG.Blueprint.NativeSporadic.M24)
      (Γ : Set ↥CFSG.Blueprint.NativeSporadic.M24),
      IsPGroup 3 E ∧ Nat.card E = 3 ^ 3 ∧ (∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) ∧
        Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ,
          (∃ Y : Subgroup ↥CFSG.Blueprint.NativeSporadic.M24, Y ≤ E ∧
            2 ≤ CFSG.Open.pRank 3 Y ∧
            g ∈ Subgroup.normalizer (Y : Set ↥CFSG.Blueprint.NativeSporadic.M24)) ∨
          ∃ u ∈ E, u ≠ 1 ∧ u ^ 3 = 1 ∧ (∀ x ∈ E, x * u = u * x) ∧
            g ∈ Subgroup.normalizer
              ((Subgroup.zpowers u : Subgroup ↥CFSG.Blueprint.NativeSporadic.M24) :
                Set ↥CFSG.Blueprint.NativeSporadic.M24) :=
  CertificateChecks.KernelCoreD2K.M24.coreGenerationZOf_M24_three

end Certificates
