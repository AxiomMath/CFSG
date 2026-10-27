module

public import CFSG.Quasithin.Background.F7Geometry

public section

namespace CFSG.Quasithin.F112Crit

open CosetGeom (graph stab ballStab nbrs)

variable {G : Type} [Group G] {G₀ G₁ G₂ : Subgroup G}

@[expose] def TrichFor (μ δ : CosetGeom G₀ G₁ G₂) (U : Subgroup G) : Prop :=
  ∀ N : Subgroup G, ballStab 1 μ ≤ N → N ≤ U ⊔ ballStab 1 μ →
    U ≤ Subgroup.normalizer (N : Set G) →
    (∀ d ∈ stab μ ⊓ stab δ, Odd (orderOf d) → d ∈ Subgroup.normalizer (N : Set G)) →
    N ≤ ballStab 1 μ ∨ U ≤ N ∨
      ((∀ n ∈ N, ∀ u ∈ U, n * u * n⁻¹ * u⁻¹ ∈ ballStab 1 μ) ∧
        (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ N) ∧
        (∀ n ∈ N, n * n ∈ ballStab 1 μ) ∧
        ∃ a ∈ U, ∃ b ∈ U, a * b * a⁻¹ * b⁻¹ ∉ ballStab 1 μ)

@[expose] def TrichConcl (δ μ' : CosetGeom G₀ G₁ G₂) (Q K : Subgroup G) : Prop :=
  K ≤ ballStab 1 μ' ∨
    (∀ ε ∈ nbrs μ', ∀ ε' ∈ nbrs μ', ε ≠ δ → ε' ≠ δ →
      ∃ r : ↥G₀, (r : G) ∈ K ∧ r • ε = ε') ∨
    ((∀ k ∈ K, ∀ g ∈ Q, k * g * k⁻¹ * g⁻¹ ∈ ballStab 1 μ') ∧
      (∀ a ∈ Q, ∀ b ∈ Q, ∃ k ∈ K, k⁻¹ * (a * b * a⁻¹ * b⁻¹) ∈ ballStab 1 μ') ∧
      (∀ k ∈ K, k * k ∈ ballStab 1 μ') ∧
      ∃ a ∈ Q, ∃ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∉ ballStab 1 μ')

end CFSG.Quasithin.F112Crit

end
