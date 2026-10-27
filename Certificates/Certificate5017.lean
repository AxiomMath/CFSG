module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Certificates.Kernel.Census.Q8Aut

public section

namespace Certificates

open Subgroup in
theorem certificate5017 : (∀ σ : MulAut (QuaternionGroup 2), (∀ y, σ (σ y) = y) →
    ¬ (∃ q : QuaternionGroup 2, ∀ y, σ y = q * y * q⁻¹) →
    ∀ x, σ x = x → x = 1 ∨ x = QuaternionGroup.a 2)
    ∧ (∀ σ γ : MulAut (QuaternionGroup 2), (∀ y, σ (σ y) = y) →
    ¬ (∃ q : QuaternionGroup 2, ∀ y, σ y = q * y * q⁻¹) → (∀ y, γ (γ (γ y)) = y) →
    (∃ y, γ y ≠ y) → ¬ (∀ y, σ (γ y) = γ (σ y)))
    ∧ (∀ σ : MulAut (QuaternionGroup 2), (∀ y, σ (σ y) = y) →
    ¬ (∃ q : QuaternionGroup 2, ∀ y, σ y = q * y * q⁻¹) →
    ∀ q, q * σ q = 1 → ∃ d, q = d * (σ d)⁻¹) :=
  ⟨Census.Q8Aut.fixed_of_outer, Census.Q8Aut.no_comm_of_outer, Census.Q8Aut.twisted_of_outer⟩

end Certificates
