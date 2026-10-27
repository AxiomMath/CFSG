module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.GF2n.Parrott.FusionE16

structure E16Config (X : Type) [Group X] where
  u : Fin 4 → X
  a : X
  b₁ : X
  ρ : X
  P : Subgroup X
  hsq : ∀ i, u i ^ 2 = 1
  hcomm : ∀ i j, Commute (u i) (u j)
  hker : ∀ c : Fin 4 → Fin 2, c ≠ 0 → (List.ofFn fun i => u i ^ (c i : ℕ)).prod ≠ 1
  act_a : a * u 0 * a⁻¹ = u 0 ∧ a * u 1 * a⁻¹ = u 1 ∧ a * u 2 * a⁻¹ = u 0 * u 2 ∧
    a * u 3 * a⁻¹ = u 0 * u 1 * u 3
  act_b : b₁ * u 0 * b₁⁻¹ = u 0 ∧ b₁ * u 1 * b₁⁻¹ = u 0 * u 1 ∧ b₁ * u 2 * b₁⁻¹ = u 2 ∧
    b₁ * u 3 * b₁⁻¹ = u 0 * u 2 * u 3
  act_ρ : ρ * u 0 * ρ⁻¹ = u 0 ∧ ρ * u 1 * ρ⁻¹ = u 2 ∧ ρ * u 2 * ρ⁻¹ = u 1 * u 2 ∧
    ρ * u 3 * ρ⁻¹ = u 3
  hSP : ∀ i, u i ∈ P
  haP : a ∈ P
  hbP : b₁ ∈ P
  hPsyl : ∃ R : Sylow 2 X, (R : Subgroup X) = P
  hPcos : ∀ p ∈ P, ∃ s ∈ Subgroup.closure (Set.range u), ∃ i j : Fin 2,
    p = s * a ^ (i : ℕ) * b₁ ^ (j : ℕ)
  hunique : ∀ E : Subgroup X, E ≤ P → CFSG.Open.IsElemAbelian 2 E → Nat.card E = 16 →
    E = Subgroup.closure (Set.range u)
  hCS : ∀ g : X, (∀ s ∈ Subgroup.closure (Set.range u), g * s = s * g) →
    g ∈ Subgroup.closure (Set.range u)

end CFSG.RankThree.GF2n.Parrott.FusionE16
