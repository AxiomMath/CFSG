module

public import CFSG.Quasithin.EmptyFaithful.S1422Elim

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

@[expose] def TitsLikeVertexFacts {G : Type*} [Group G] (H L2 : Subgroup G) : Prop :=
  ∃ E F : Subgroup G,
    (∀ x, x ∈ E ↔ x ∈ pCoreOf 2 H ∧ ∀ y ∈ pCoreOf 2 H,
        x * y * x⁻¹ * y⁻¹ ∈ quasithinOmegaOneCenter (H ⊓ L2)) ∧
    (∀ x, x ∈ F ↔ x ∈ pCoreOf 2 H ∧ ∀ e ∈ E, x * e = e * x) ∧
    (∀ e ∈ E, e * e = 1) ∧ (∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) ∧
    Nat.card (pCoreOf 2 H) = 16 * Nat.card F ∧ Nat.card F ≤ 2 * Nat.card E ∧
    (∀ x ∈ E, (∀ y ∈ pCoreOf 2 H, x * y = y * x) → x ∈ quasithinOmegaOneCenter (H ⊓ L2)) ∧
    (∀ x ∈ pCoreOf 2 H, ∀ y ∈ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ F) ∧
    (∀ Q : Subgroup G, E ≤ Q → Q ≤ pCoreOf 2 H → H ≤ Subgroup.normalizer (Q : Set G) →
      (∀ x ∈ Q, (∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ quasithinOmegaOneCenter (H ⊓ L2)) → x ∈ E) ∨
      (∀ x ∈ Q, x * x = 1 → x ∈ E)) ∧
    (∃ j ∈ pCoreOf 2 H, j ∉ F ∧ j * j = 1) ∧
    (∀ j ∈ pCoreOf 2 H, j ∉ F → j * j = 1 → ∀ j' ∈ pCoreOf 2 H, j' ∉ F → j' * j' = 1 →
      ∃ h ∈ H, h * j * h⁻¹ = j') ∧
    ∃ c ∈ H, c ^ 5 = 1 ∧ ∀ x ∈ pCoreOf 2 H, x ∉ F → c * x * c⁻¹ * x⁻¹ ∉ F

@[expose] def TitsAmalgamLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H L2 : Subgroup G), CaseTits H L2 → TitsLikeVertexFacts H L2

@[expose] def TwoF4AmalgamLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H L2 : Subgroup G), Case2F4 H L2 → TitsLikeVertexFacts H L2

end CFSG.Quasithin
