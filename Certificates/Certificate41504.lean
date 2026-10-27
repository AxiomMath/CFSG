module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import Certificates.Kernel.LocalComp.L34Two.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.PSL3Four in
theorem certificate41504 : ∃ B₀ : Subgroup (Equiv.Perm (Fin 42)), B₀ ≤ CFSG.ComponentClassification.PSL3Four.S ∧ Nat.card B₀ = 9 ∧
    ∀ r ∈ R, r ^ 256 = 1 → (∀ b ∈ B₀, b * r = r * b) ∨
      ∃ w ∈ Subgroup.closure {x | ∃ c ∈ B₀, x = c * r * c⁻¹}, w ^ 256 ≠ 1 := KernelLC.L34Two.facts41504

end Certificates
