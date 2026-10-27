module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.Sporadic.J4Schreier

open MulAction

theorem card_le_card_stabilizer {M X : Type*} [Group M] [MulAction M X] {G₀ G₁ : Subgroup M}
    [Finite G₀] (h10 : G₁ ≤ G₀) {b : X} (hfix : ∀ g ∈ G₁, g • b = b) :
    Nat.card G₁ ≤ Nat.card (stabilizer G₀ b) := by
  refine Nat.card_le_card_of_injective
    (fun g => (⟨⟨g, h10 g.2⟩, hfix g g.2⟩ : stabilizer G₀ b)) fun g h e => ?_
  have := congrArg (fun s : stabilizer G₀ b => ((s : G₀) : M)) e
  exact Subtype.ext this

theorem card_eq_orbit_mul_stabilizer {M X : Type*} [Group M] [MulAction M X] (G : Subgroup M)
    [Finite G] (b : X) :
    Nat.card G = (orbit G b).ncard * Nat.card (stabilizer G b) := by
  rw [← index_stabilizer, mul_comm, Subgroup.card_mul_index]

theorem orbit_ncard_le {M X : Type*} [Group M] [MulAction M X] (G : Subgroup M) [Finite G]
    (b : X) : (orbit G b).ncard ≤ Nat.card G := by
  rw [card_eq_orbit_mul_stabilizer G b]
  exact Nat.le_mul_of_pos_right _ Nat.card_pos

theorem card_ge_of_orbit_chain {M X : Type*} [Group M] [MulAction M X] {G₀ G₁ G₂ : Subgroup M}
    [Finite G₀] (h10 : G₁ ≤ G₀) (h21 : G₂ ≤ G₁) {b₀ b₁ : X} (b₂ : X)
    (hf1 : ∀ g ∈ G₁, g • b₀ = b₀) (hf2 : ∀ g ∈ G₂, g • b₁ = b₁) :
    (orbit G₀ b₀).ncard * (orbit G₁ b₁).ncard * (orbit G₂ b₂).ncard ≤ Nat.card G₀ := by
  have : Finite G₁ := Finite.of_injective _ (Subgroup.inclusion_injective h10)
  have : Finite G₂ := Finite.of_injective _ (Subgroup.inclusion_injective h21)
  have e0 := card_eq_orbit_mul_stabilizer G₀ b₀
  have e1 := card_eq_orbit_mul_stabilizer G₁ b₁
  have s1 := card_le_card_stabilizer h10 hf1
  have s2 := card_le_card_stabilizer h21 hf2
  have o2 := orbit_ncard_le G₂ b₂
  calc (orbit G₀ b₀).ncard * (orbit G₁ b₁).ncard * (orbit G₂ b₂).ncard
      ≤ (orbit G₀ b₀).ncard * (orbit G₁ b₁).ncard * Nat.card (stabilizer G₁ b₁) :=
        Nat.mul_le_mul_left _ (o2.trans s2)
    _ = (orbit G₀ b₀).ncard * Nat.card G₁ := by rw [mul_assoc, ← e1]
    _ ≤ (orbit G₀ b₀).ncard * Nat.card (stabilizer G₀ b₀) := Nat.mul_le_mul_left _ s1
    _ = Nat.card G₀ := e0.symm

end CFSG.Sporadic.J4Schreier
