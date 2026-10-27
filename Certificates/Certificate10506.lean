module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo1Defs
import Certificates.Kernel.EaLat10506.Glue

public section

namespace Certificates

open CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K CFSG.Sporadic.Co1.Cover
  CFSG.Sporadic.SmallF2 in
theorem certificate10506 :     Nat.card t24 = 2 ^ 10 ∧ (∀ t ∈ t24, rho t (toVecD 11 3) = toVecD 11 3) ∧
    ∀ K : Subgroup PM24, K ≤ t24 → K ≠ ⊥ → (∀ x ∈ K, ∀ y ∈ K, x * y = y * x) →
      (∀ x ∈ K, x * x = 1) →
      Nat.card K * Nat.card {v : Fin 11 → ZMod 2 // ∀ p ∈ K, rho p v = v} ≤ 2 ^ 10 :=
  CertificateChecks.KernelEaLat10506.t24_facts_of_checks

end Certificates
