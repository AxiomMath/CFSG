module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open
open scoped commutatorElement

theorem x101Cover_commutator_central {H : Type} [Group H] {c d x y : H}
    (hc : c ∈ Subgroup.center H) (hd : d ∈ Subgroup.center H) : ⁅c * x, d * y⁆ = ⁅x, y⁆ := by
  have h1 : ∀ g : H, c * g * c⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hc g, mul_inv_cancel_right]
  have h2 : ∀ g : H, d * g * d⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hd g, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc c * x * (d * y) * (c * x)⁻¹ * (d * y)⁻¹
      = c * (x * d * y * x⁻¹) * c⁻¹ * (y⁻¹ * d⁻¹) := by group
    _ = x * d * y * x⁻¹ * (y⁻¹ * d⁻¹) := by rw [h1]
    _ = x * (d * (y * x⁻¹ * y⁻¹) * d⁻¹) := by group
    _ = x * (y * x⁻¹ * y⁻¹) := by rw [h2]
    _ = x * y * x⁻¹ * y⁻¹ := by group

private theorem x101Cover_map_top {H : Type} [Group H] (K : Subgroup H) :
    (⊤ : Subgroup K).map K.subtype = K := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem x101Cover_commutator_eq_top_iff {H : Type} [Group H] (K : Subgroup H) :
    commutator K = ⊤ ↔ ⁅K, K⁆ = K := by
  have hm : (commutator K).map K.subtype = ⁅K, K⁆ := by
    show Subgroup.map K.subtype ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⁅K, K⁆
    rw [Subgroup.map_commutator, x101Cover_map_top]
  constructor
  · intro h
    rw [← hm, h, x101Cover_map_top]
  · intro h
    apply Subgroup.map_injective (f := K.subtype) Subtype.val_injective
    rw [hm, h, x101Cover_map_top]

private theorem x101Cover_bot_ne_top {H : Type} [Group H] [Nontrivial H] :
    (⊥ : Subgroup H) ≠ ⊤ := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_pair_ne H
  have hx : x ∈ (⊥ : Subgroup H) := by rw [h]; exact Subgroup.mem_top x
  have hy : y ∈ (⊥ : Subgroup H) := by rw [h]; exact Subgroup.mem_top y
  exact hxy ((Subgroup.mem_bot.1 hx).trans (Subgroup.mem_bot.1 hy).symm)

theorem x101Cover_center_eq_bot {H : Type} [Group H] [IsSimpleGroup H]
    (hp : commutator H = ⊤) : Subgroup.center H = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center H) with h | h
  · exact h
  · exact absurd (((commutator_eq_bot_iff_center_eq_top H).2 h).symm.trans hp)
      x101Cover_bot_ne_top

theorem x101Cover_exists_noncomm {H : Type} [Group H] [Nontrivial H]
    (hz : Subgroup.center H = ⊥) : ∃ a b : H, a * b ≠ b * a := by
  by_contra hcon
  have hall : ∀ a b : H, a * b = b * a := fun a b => by
    by_contra h
    exact hcon ⟨a, b, h⟩
  apply x101Cover_bot_ne_top (H := H)
  rw [← hz, eq_top_iff]
  intro g _
  exact Subgroup.mem_center_iff.2 fun h => hall h g

theorem x101Cover_classical_of_mulEquiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H) {n p f : ℕ} (h : StatedClassicalModel H .PSU n p f) :
    StatedClassicalModel G .PSU n p f := by
  obtain ⟨hadm, K, hK, hfin, hcard, ⟨φ⟩⟩ := h
  exact ⟨hadm, K, hK, hfin, hcard, ⟨e.trans φ⟩⟩

end CFSG.GGQ2Prime
