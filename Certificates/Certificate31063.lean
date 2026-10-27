module

public import CFSG.Open.LocalVocabulary
public import CFSG.Sporadic.Schreier.RuDefs
import Certificates.Kernel.CoreD2K.RuFive.Glue

public section

namespace Certificates

theorem certificate31063 :
    ∃ E : Subgroup ↥CFSG.Sporadic.RuSchreier.ruP, Nat.card E = 5 ^ 3 ∧ (∀ x ∈ E, x ^ 5 = 1) ∧
      (∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) ∧
      ∀ A : Subgroup ↥CFSG.Sporadic.RuSchreier.ruP, A ≤ E → CFSG.Open.IsElemAbelian 5 A →
        Nat.card A = 5 ^ 2 →
        ∃ Γ : Set ↥CFSG.Sporadic.RuSchreier.ruP, Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ,
          ∃ Q : Subgroup ↥CFSG.Sporadic.RuSchreier.ruP, Q ≤ A ∧ 1 ≤ CFSG.Open.pRank 5 Q ∧
            g ∈ Subgroup.normalizer (Q : Set ↥CFSG.Sporadic.RuSchreier.ruP) :=
  CertificateChecks.KernelCoreD2K.RuFive.coreGenerationOneOf_ruP_five

end Certificates
