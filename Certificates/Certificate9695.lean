module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import Certificates.Kernel.LocalComp.L34Fix.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.PSL3Four in
theorem certificate9695 : ∃ (H₀ : Subgroup (Equiv.Perm (Fin 42))) (M : Fin 4 → Subgroup (Equiv.Perm (Fin 42))),
    H₀ ≤ CFSG.ComponentClassification.PSL3Four.R ∧ Nat.card H₀ = 27 ∧ (∀ k, Nat.card (M k) = 9) ∧
    (∀ u ∈ H₀, ∀ v ∈ H₀, u * v = v * u → ∃ k, u ∈ M k ∧ v ∈ M k) ∧ M 0 ≤ CFSG.ComponentClassification.PSL3Four.S ∧
    ∀ k : Fin 4, k ≠ 0 →
      Subgroup.closure {s | s ∈ CFSG.ComponentClassification.PSL3Four.S ∧ ∃ r ∈ M k, r ≠ 1 ∧ r * s * r⁻¹ = s} = CFSG.ComponentClassification.PSL3Four.S := KernelLC.L34Fix.facts9695

end Certificates
