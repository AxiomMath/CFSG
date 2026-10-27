module

public import CFSG.Open.LocalVocabulary
import Certificates.Kernel.CoreD2K.Co3Cent.Glue
public import CFSG.Sporadic.Schreier.Co3CertBase

public section

namespace Certificates

theorem certificate1322010 :
    ∃ E : Subgroup ↥CFSG.Sporadic.Schreier.Co3.co3P, Nat.card E = 5 ^ 3 ∧
      ∀ A : Subgroup ↥CFSG.Sporadic.Schreier.Co3.co3P, A ≤ E → CFSG.Open.IsElemAbelian 5 A →
        Nat.card A = 5 ^ 2 →
        ∃ Γ : Set ↥CFSG.Sporadic.Schreier.Co3.co3P, Subgroup.closure Γ = ⊤ ∧
          ∀ g ∈ Γ, ∃ y ∈ A, y ≠ 1 ∧ g * y = y * g :=
  CertificateChecks.KernelCoreD2K.Co3Cent.exists_cent_gens_co3P

end Certificates
