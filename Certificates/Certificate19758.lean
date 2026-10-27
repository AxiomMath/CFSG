module

public import CFSG.Open.LocalVocabulary
public import CFSG.Sporadic.Co2Cert.Cert
import Certificates.Kernel.CoreD2K.Co2.Glue

public section

namespace Certificates

theorem certificate19758 :
    ∃ E : Subgroup ↥CFSG.Sporadic.Co2Cert.co2P, Nat.card E = 5 ^ 3 ∧
      ∀ A : Subgroup ↥CFSG.Sporadic.Co2Cert.co2P, A ≤ E → CFSG.Open.IsElemAbelian 5 A →
        Nat.card A = 5 ^ 2 →
        ∃ Γ : Set ↥CFSG.Sporadic.Co2Cert.co2P, Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ,
          ∃ Q : Subgroup ↥CFSG.Sporadic.Co2Cert.co2P, Q ≤ A ∧ Q ≠ ⊥ ∧
            g ∈ Subgroup.normalizer (Q : Set ↥CFSG.Sporadic.Co2Cert.co2P) :=
  CertificateChecks.KernelCoreD2K.Co2.exists_normalizer_gens_co2P

end Certificates
