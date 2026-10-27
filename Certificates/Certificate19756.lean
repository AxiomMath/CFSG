module

public import CFSG.Open.LocalVocabulary
import Certificates.Kernel.CoreD2K.J2.Glue
public import CFSG.Sporadic.Schreier.PairJ2CertBase

public section

namespace Certificates

theorem certificate19756 :
    ∃ E : Subgroup ↥CFSG.Sporadic.Schreier.j2P, Nat.card E = 3 ^ 3 ∧
      ∀ A : Subgroup ↥CFSG.Sporadic.Schreier.j2P, A ≤ E → CFSG.Open.IsElemAbelian 3 A →
        Nat.card A = 3 ^ 2 →
        ∃ Γ : Set ↥CFSG.Sporadic.Schreier.j2P, Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ,
          ∃ Q : Subgroup ↥CFSG.Sporadic.Schreier.j2P, Q ≤ A ∧ Q ≠ ⊥ ∧
            g ∈ Subgroup.normalizer (Q : Set ↥CFSG.Sporadic.Schreier.j2P) :=
  CertificateChecks.KernelCoreD2K.J2.exists_normalizer_gens_j2P

end Certificates
