module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import Certificates.Kernel.L34Four.Final

public section

namespace Certificates

open CFSG.ComponentClassification.PSL3Four Subgroup in
theorem certificate55104 : (∀ t ∈ R, t * t = 1 → t ≠ 1 → ∃ r ∈ [r₁, r₂, r₃, r₄], ∃ g ∈ R, t = g * r * g⁻¹) ∧
    ∀ r ∈ [r₁, r₂, r₃, r₄], ∀ w ∈ R ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 42))),
      w * w = 1 → w ≠ 1 → w ≠ r →
        Nat.card ↥((R ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 42)))) ⊓
          centralizer ({w} : Set (Equiv.Perm (Fin 42)))) ∣ 2 ^ 30 * 3 ^ 30 :=
  CFSG.KD.L34Four.l34Four_facts

end Certificates
