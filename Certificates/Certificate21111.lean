module

public import CFSG.LargeExtraspecial.S63CD4Model
import Certificates.Kernel.S63K.I21111

public section

namespace Certificates

open CertificateChecks

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin Subgroup in
theorem certificate21111 :
    (∀ k < 8, d4GenG k * d4GenG k = 1) ∧ Nat.card d4U = 4096 ∧
      Nat.card (centralizer ({d4z} : Set trialityGroup8)) * 819 ≤ Nat.card trialityGroup8 ∧
      Nat.card (centralizer ({d4t} : Set trialityGroup8)) * 68796 ≤ Nat.card trialityGroup8 ∧
      ∀ u ∈ d4U, u * u = 1 → u ≠ 1 → ∃ c, u = c * d4z * c⁻¹ ∨ u = c * d4t * c⁻¹ := KernelS63.I21111.facts

end Certificates
