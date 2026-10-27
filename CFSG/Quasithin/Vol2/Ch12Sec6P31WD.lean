module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WGrp
public import Mathlib.Tactic.NormNum.Prime

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31D

@[expose] def ThreeRankLE2 (G : Type*) [Group G] : Prop :=
  ∀ x y z : G, x ^ 3 = 1 → y ^ 3 = 1 → z ^ 3 = 1 → Commute x y → Commute x z → Commute y z →
    (∀ a b c : ℕ, x ^ a * y ^ b * z ^ c = 1 → 3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c) → False

theorem borel_pair_maximal_overgroups {G : Type*} [Group G] {K₁ K₂ B₁ B₂ Y : Subgroup G}
    [IsSimpleGroup K₁] [IsSimpleGroup K₂]
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hK : K₁ ⊓ K₂ = ⊥)
    (hB₁le : B₁ ≤ K₁) (hB₂le : B₂ ≤ K₂)
    (hB₁ : IsCoatom (B₁.subgroupOf K₁)) (hB₂ : IsCoatom (B₂.subgroupOf K₂))
    (hB₁ne : B₁ ≠ ⊥) (hBY : B₁ ⊔ B₂ ≤ Y) (hYK : Y ≤ K₁ ⊔ K₂)
    {t : G} (htK₁ : ∀ x ∈ K₁, t * x * t⁻¹ ∈ K₂) (htK₂ : ∀ x ∈ K₂, t * x * t⁻¹ ∈ K₁)
    (ht : t ∈ Subgroup.normalizer Y) :
    (Y ⊓ K₁ = B₁ ∧ Y ⊓ K₂ = B₂ ∧ Y = B₁ ⊔ B₂) ∨
      (Y ⊓ K₁ = K₁ ∧ Y ⊓ K₂ = K₂ ∧ Y = K₁ ⊔ K₂) := by
  obtain ⟨hY1, hY2, hdec⟩ :=
    P31Grp.eq_of_le_prod_of_maximal hcomm hK hB₁le hB₂le hB₁ hB₂ hB₁ne hBY hYK
  have hnorm : ∀ x : G, t * x * t⁻¹ ∈ Y → x ∈ Y := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp ht x).mpr hx
  have hB₁K : B₁ ≠ K₁ := by
    intro h
    apply hB₁.1
    rw [h, Subgroup.subgroupOf_self]
  have hswap1 : Y ⊓ K₂ = K₂ → Y ⊓ K₁ = K₁ := by
    intro h2
    have hK2Y : K₂ ≤ Y := inf_eq_right.mp h2
    apply le_antisymm inf_le_right
    refine le_inf ?_ le_rfl
    intro x hx
    exact hnorm x (hK2Y (htK₁ x hx))
  have hswap2 : Y ⊓ K₁ = K₁ → Y ⊓ K₂ = K₂ := by
    intro h1
    have hK1Y : K₁ ≤ Y := inf_eq_right.mp h1
    apply le_antisymm inf_le_right
    refine le_inf ?_ le_rfl
    intro x hx
    exact hnorm x (hK1Y (htK₂ x hx))
  rcases hY1 with h1 | h1
  · have h2 : Y ⊓ K₂ = B₂ := by
      rcases hY2 with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans (hswap1 h2)) hB₁K
    left
    refine ⟨h1, h2, ?_⟩
    calc Y = (Y ⊓ K₁) ⊔ (Y ⊓ K₂) := hdec
      _ = B₁ ⊔ B₂ := by rw [h1, h2]
  · have h2 : Y ⊓ K₂ = K₂ := hswap2 h1
    right
    refine ⟨h1, h2, ?_⟩
    calc Y = (Y ⊓ K₁) ⊔ (Y ⊓ K₂) := hdec
      _ = K₁ ⊔ K₂ := by rw [h1, h2]

theorem exists_pSubgroup_of_moved {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {T L M Nh Q TL : Subgroup G} (hT : IsPGroup 2 T)
    (hLM : M ≤ Subgroup.normalizer L) (hNhM : Nh ≤ M) (hTNh : T ≤ Subgroup.normalizer Nh)
    (hTLn : T ≤ Subgroup.normalizer L) (hTLdef : TL = T ⊓ L) (hQT : Q ≤ T) (hQNh : Q ≤ Nh)
    (hNhQ : Nh ≤ Subgroup.normalizer Q) (hNhQp : ∀ x ∈ Nh, ∃ n : ℕ, x ^ (p ^ n) ∈ Q)
    {n r : G} (hn : n ∈ Nh) (hr : r ∈ TL) (hmoved : n * r * n⁻¹ * r⁻¹ ∉ Q) :
    ∃ P : Subgroup G, P ≤ L ∧ P ≠ ⊥ ∧ IsPGroup p P ∧
      (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G) := by
  refine P31Grp.exists_pSubgroup_permuting hp hp2 hT hLM hNhM hTNh hTLn hTLdef hQT hQNh hNhQ
    hNhQp ?_
  intro hle
  have hc := Subgroup.commutator_mem_commutator hn hr
  rw [commutatorElement_def] at hc
  exact hmoved (hle hc)

end CFSG.Quasithin.H13.P31D
