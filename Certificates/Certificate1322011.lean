module

public import CFSG.Open.LocalVocabulary
public import CFSG.Sporadic.Co2Cert.Cert
import Certificates.Kernel.CoreD2K.Co2Cent.Glue

public section

namespace Certificates

theorem certificate1322011 :
    ∃ E : Subgroup ↥CFSG.Sporadic.Co2Cert.co2P, Nat.card E = 5 ^ 3 ∧
      ∀ A : Subgroup ↥CFSG.Sporadic.Co2Cert.co2P, A ≤ E → CFSG.Open.IsElemAbelian 5 A →
        Nat.card A = 5 ^ 2 →
        ∃ Γ : Set ↥CFSG.Sporadic.Co2Cert.co2P, Subgroup.closure Γ = ⊤ ∧
          ∀ g ∈ Γ, ∃ y ∈ A, y ≠ 1 ∧ g * y = y * g :=
  CertificateChecks.KernelCoreD2K.Co2Cent.exists_cent_gens_co2P

end Certificates
