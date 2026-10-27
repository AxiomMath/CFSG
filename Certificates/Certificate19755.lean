module

public import CFSG.Open.LocalVocabulary
public import CFSG.Sporadic.Schreier.RuDefs
import Certificates.Kernel.CoreD2K.RuThree.Glue

public section

namespace Certificates

theorem certificate19755 :
    ∃ E : Subgroup ↥CFSG.Sporadic.RuSchreier.ruP, IsPGroup 3 E ∧ Nat.card E = 3 ^ 3 ∧
      ∀ A : Subgroup ↥CFSG.Sporadic.RuSchreier.ruP, A ≤ E → CFSG.Open.IsElemAbelian 3 A →
        Nat.card A = 3 ^ 2 →
        ∃ Γ : Set ↥CFSG.Sporadic.RuSchreier.ruP, Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ,
          (∃ Y : Subgroup ↥CFSG.Sporadic.RuSchreier.ruP, Y ≤ E ∧ 2 ≤ CFSG.Open.pRank 3 Y ∧
            g ∈ Subgroup.normalizer (Y : Set ↥CFSG.Sporadic.RuSchreier.ruP)) ∨
          ∃ Q : Subgroup ↥CFSG.Sporadic.RuSchreier.ruP, Q ≤ A ∧ 1 ≤ CFSG.Open.pRank 3 Q ∧
            g ∈ Subgroup.normalizer (Q : Set ↥CFSG.Sporadic.RuSchreier.ruP) :=
  CertificateChecks.KernelCoreD2K.RuThree.coreGenerationVOf_ruP_three

end Certificates
