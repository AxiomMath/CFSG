module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.QuasithinUnique.A5.Delta5 (pact isEven)

@[expose] def OrbitTwo (σ τ π : Equiv.Perm (Fin 5)) (x : Fin 5 → ZMod 2) : Prop :=
  pact π x ≠ x ∧ ∀ ρ : Equiv.Perm (Fin 5), ρ * ρ = 1 → ρ * σ = σ * ρ → ρ * τ = τ * ρ →
    pact ρ x = x ∨ pact ρ x = pact π x

instance (σ τ π : Equiv.Perm (Fin 5)) : DecidablePred (OrbitTwo σ τ π) := fun x => by
  unfold OrbitTwo; infer_instance

theorem perm5_orbit_two : ∀ σ τ : Equiv.Perm (Fin 5),
    (σ * σ = 1 ∧ τ * τ = 1 ∧ σ * τ = τ * σ ∧ σ ≠ 1 ∧ τ ≠ 1 ∧ σ ≠ τ) →
    ∃ x : Fin 5 → ZMod 2, isEven x ∧
      (OrbitTwo σ τ σ x ∨ OrbitTwo σ τ τ x ∨ OrbitTwo σ τ (σ * τ) x) := by
  decide +kernel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
