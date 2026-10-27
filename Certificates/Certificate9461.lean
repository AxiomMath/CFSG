module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import Certificates.Kernel.LocalComp.L34F9461

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.PSL3Four in
theorem certificate9461 : ∃ z₀ ∈ S, z₀ ^ 3 = 1 ∧ z₀ ≠ 1 ∧
    ∀ x ∈ R, x ^ 3 = 1 → x * z₀ = z₀ * x → x ∉ S →
      ∀ Y : Subgroup (Equiv.Perm (Fin 42)),
        (∀ c ∈ S, c * z₀ = z₀ * c ∨ c * x = x * c ∨ c * (z₀ * x) = z₀ * x * c ∨
          c * (z₀ ^ 2 * x) = z₀ ^ 2 * x * c → c ∈ Y) → S ≤ Y :=
  KernelLC.L34F946.spec9461

end Certificates
