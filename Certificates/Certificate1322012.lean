module

public import CFSG.Open.LocalVocabulary
public import CFSG.Sporadic.Schreier.RuDefs
import Certificates.Kernel.CoreD2K.RuCent.Glue

public section

namespace Certificates

theorem certificate1322012 :
    ∃ E : Subgroup ↥CFSG.Sporadic.RuSchreier.ruP, Nat.card E = 5 ^ 3 ∧
      ∀ A : Subgroup ↥CFSG.Sporadic.RuSchreier.ruP, A ≤ E → CFSG.Open.IsElemAbelian 5 A →
        Nat.card A = 5 ^ 2 →
        ∃ Γ : Set ↥CFSG.Sporadic.RuSchreier.ruP, Subgroup.closure Γ = ⊤ ∧
          ∀ g ∈ Γ, ∃ y ∈ A, y ≠ 1 ∧ g * y = y * g :=
  CertificateChecks.KernelCoreD2K.RuCent.exists_cent_gens_ruP

end Certificates
