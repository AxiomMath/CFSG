module

public import CFSG.Open.LocalVocabulary
import Certificates.Kernel.CoreD2K.Co3.Glue
public import CFSG.Sporadic.Schreier.Co3CertBase

public section

namespace Certificates

theorem certificate19757 :
    ∃ E : Subgroup ↥CFSG.Sporadic.Schreier.Co3.co3P, Nat.card E = 5 ^ 3 ∧
      ∀ A : Subgroup ↥CFSG.Sporadic.Schreier.Co3.co3P, A ≤ E → CFSG.Open.IsElemAbelian 5 A →
        Nat.card A = 5 ^ 2 →
        ∃ Γ : Set ↥CFSG.Sporadic.Schreier.Co3.co3P, Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ,
          ∃ Q : Subgroup ↥CFSG.Sporadic.Schreier.Co3.co3P, Q ≤ A ∧ Q ≠ ⊥ ∧
            g ∈ Subgroup.normalizer (Q : Set ↥CFSG.Sporadic.Schreier.Co3.co3P) :=
  CertificateChecks.KernelCoreD2K.Co3.exists_normalizer_gens_co3P

end Certificates
