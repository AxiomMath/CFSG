module

public import Certificates.Certificate25002
import Certificates.Kernel.EvenSporSuz.F2Glue1379102

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoSuz Cert25002 in
theorem certificate1379102 : Nat.card (⁅⁅S, S⁆, S⁆ : Subgroup GL12) = 2 ^ 7 ∧
    Nat.card (⁅⁅S, S⁆, S⁆ ⊓
      Subgroup.centralizer ((⁅⁅S, S⁆, S⁆ : Subgroup GL12) : Set GL12) : Subgroup GL12) = 32 ∧
    (∀ x ∈ (⁅⁅S, S⁆, S⁆ ⊓
      Subgroup.centralizer ((⁅⁅S, S⁆, S⁆ : Subgroup GL12) : Set GL12) : Subgroup GL12),
      x * x = 1) ∧
    ∃ Q : Subgroup GL12, Q ≤ S ∧ (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧ (∀ x ∈ Q, x * x = 1) ∧
      Nat.card Q = 8 ∧ ∀ i < 7, ∀ u : GL12, vm u = ofMt (coverGS.mats.getD i oneM) →
        u ∈ S ⊔ (AB ⊓ Subgroup.centralizer (Q : Set GL12)) := KernelF21379102.cert

end Certificates
