module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreData
import Certificates.Kernel.Sporadic.Fi22.C9567Sound

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.Monster.B.Co2 in
theorem certificate9567 : ∀ G₁ G₂ : Equiv.Perm (Fin 3510), Rep 3510 g1A G₁ → Rep 3510 g2A G₂ →
    ∃ a ∈ Subgroup.closure ({G₁, G₂} : Set (Equiv.Perm (Fin 3510))),
      ∃ b ∈ Subgroup.closure ({G₁, G₂} : Set (Equiv.Perm (Fin 3510))),
        a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b = b * a ∧
          ∀ i j : ℕ, i < 3 → j < 3 → (i ≠ 0 ∨ j ≠ 0) → a ^ i * b ^ j ≠ 1 :=
  fun _ _ h₁ h₂ => KernelSpor.Fi22C9567.e9 h₁ h₂

end Certificates
