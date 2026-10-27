module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.Quasithin.H13.U43

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem u43_relIndex_dvd {M S M' : Subgroup G} (hMS : M ≤ S) (hMnorm : ∀ s ∈ S, ∀ m ∈ M,
    s * m * s⁻¹ ∈ M) (hM' : M' ≤ S) (hM : Nat.card M = 81) {n : ℕ} (hS : Nat.card S = 81 * n) :
    M.relIndex M' ∣ n := by
  have hN : (M.subgroupOf S).Normal :=
    ⟨fun m hm g => by
      have h := hMnorm g g.2 m (by simpa [Subgroup.mem_subgroupOf] using hm)
      simpa [Subgroup.mem_subgroupOf] using h⟩
  have h1 : (M.subgroupOf S).relIndex (M'.subgroupOf S) ∣ (M.subgroupOf S).index :=
    Subgroup.relIndex_dvd_index_of_normal _ _
  rw [Subgroup.relIndex_subgroupOf hM'] at h1
  have h2 : Nat.card (M.subgroupOf S) * (M.subgroupOf S).index = Nat.card S :=
    Subgroup.card_mul_index _
  have h3 : Nat.card (M.subgroupOf S) = 81 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMS).toEquiv, hM]
  rw [h3, hS] at h2
  have h4 : (M.subgroupOf S).index = n := by omega
  rwa [h4] at h1

theorem u43_unique_abelian_81 {M S M' : Subgroup G} (hMS : M ≤ S)
    (hMnorm : ∀ s ∈ S, ∀ m ∈ M, s * m * s⁻¹ ∈ M) (hM : Nat.card M = 81)
    {n : ℕ} (hn : n = 3 ∨ n = 9) (hS : Nat.card S = 81 * n)
    (hF1 : ∀ x ∈ S, x ∉ M → Nat.card {m : ↥M // x * m = m * x} ≤ 9)
    (hF2 : ∀ x ∈ S, x ∉ M → ∀ y ∈ S, y ∉ M → x⁻¹ * y ∉ M → (x * x)⁻¹ * y ∉ M →
      Nat.card {m : ↥M // x * m = m * x ∧ y * m = m * y} ≤ 3)
    (hM'S : M' ≤ S) (hM'ab : ∀ a ∈ M', ∀ b ∈ M', a * b = b * a) (hM' : Nat.card M' = 81) :
    M' = M := by
  by_contra hne
  have hnot : ∃ x ∈ M', x ∉ M := by
    by_contra h
    push Not at h
    exact hne (Subgroup.eq_of_le_of_card_ge h (by rw [hM, hM']))
  obtain ⟨x, hxM', hxM⟩ := hnot
  have hxS : x ∈ S := hM'S hxM'
  have hKM : M ⊓ M' ≤ M := inf_le_left
  have hKM' : M ⊓ M' ≤ M' := inf_le_right
  have hK9 : Nat.card ↥(M ⊓ M') ≤ 9 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun k : ↥(M ⊓ M') => (⟨⟨k.1, hKM k.2⟩, hM'ab x hxM' k (hKM' k.2)⟩ :
        {m : ↥M // x * m = m * x})) ?_) (hF1 x hxS hxM)
    intro a b hab
    exact Subtype.ext (congrArg (fun t : {m : ↥M // x * m = m * x} => (t.1 : G)) hab)
  have h5 : M.relIndex M' * Nat.card ↥(M ⊓ M') = 81 := by
    rw [Subgroup.relIndex_mul_card, hM']
  have h6 : M.relIndex M' ∣ n := u43_relIndex_dvd hMS hMnorm hM'S hM hS
  rcases hn with rfl | rfl
  · have h7 : M.relIndex M' ≤ 3 := Nat.le_of_dvd (by decide) h6
    have := Nat.mul_le_mul h7 hK9
    omega
  · have h7 : M.relIndex M' ≤ 9 := Nat.le_of_dvd (by decide) h6
    have h8 : M.relIndex M' * Nat.card ↥(M ⊓ M') ≤ M.relIndex M' * 9 :=
      Nat.mul_le_mul_left _ hK9
    have h9 : M.relIndex M' = 9 := by omega
    have h10 : Nat.card ↥(M ⊓ M') = 9 := by rw [h9] at h5; omega
    have hy : ∃ y ∈ M', y ∉ (M ⊓ M' : Subgroup G) ∧ x⁻¹ * y ∉ (M ⊓ M' : Subgroup G) ∧
        (x * x)⁻¹ * y ∉ (M ⊓ M' : Subgroup G) := by
      by_contra hcon
      push Not at hcon
      have hsub : (M' : Set G) ⊆ ((M ⊓ M' : Subgroup G) : Set G) ∪
          ((fun a => x * a) '' ((M ⊓ M' : Subgroup G) : Set G)) ∪
          ((fun a => (x * x) * a) '' ((M ⊓ M' : Subgroup G) : Set G)) := by
        intro y hy
        by_cases h1 : y ∈ (M ⊓ M' : Subgroup G)
        · exact Or.inl (Or.inl h1)
        · by_cases h2 : x⁻¹ * y ∈ (M ⊓ M' : Subgroup G)
          · exact Or.inl (Or.inr ⟨x⁻¹ * y, h2, mul_inv_cancel_left x y⟩)
          · have h3 := hcon y hy h1 h2
            exact Or.inr ⟨(x * x)⁻¹ * y, h3, mul_inv_cancel_left (x * x) y⟩
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      have hu1 := Set.ncard_union_le (((M ⊓ M' : Subgroup G) : Set G) ∪
          ((fun a => x * a) '' ((M ⊓ M' : Subgroup G) : Set G)))
        ((fun a => (x * x) * a) '' ((M ⊓ M' : Subgroup G) : Set G))
      have hu2 := Set.ncard_union_le ((M ⊓ M' : Subgroup G) : Set G)
        ((fun a => x * a) '' ((M ⊓ M' : Subgroup G) : Set G))
      have hi1 : ((fun a => x * a) '' ((M ⊓ M' : Subgroup G) : Set G)).ncard =
          ((M ⊓ M' : Subgroup G) : Set G).ncard :=
        Set.ncard_image_of_injective _ (mul_right_injective x)
      have hi2 : ((fun a => (x * x) * a) '' ((M ⊓ M' : Subgroup G) : Set G)).ncard =
          ((M ⊓ M' : Subgroup G) : Set G).ncard :=
        Set.ncard_image_of_injective _ (mul_right_injective (x * x))
      have hc1 : ((M ⊓ M' : Subgroup G) : Set G).ncard = 9 := by
        rw [← Nat.card_coe_set_eq]; exact h10
      have hc2 : (M' : Set G).ncard = 81 := by
        rw [← Nat.card_coe_set_eq]; exact hM'
      omega
    obtain ⟨y, hyM', hy1, hy2, hy3⟩ := hy
    have hyS : y ∈ S := hM'S hyM'
    have hyM : y ∉ M := fun h => hy1 ⟨h, hyM'⟩
    have hy2' : x⁻¹ * y ∉ M := fun h => hy2 ⟨h, M'.mul_mem (M'.inv_mem hxM') hyM'⟩
    have hy3' : (x * x)⁻¹ * y ∉ M := fun h =>
      hy3 ⟨h, M'.mul_mem (M'.inv_mem (M'.mul_mem hxM' hxM')) hyM'⟩
    have h12 : Nat.card ↥(M ⊓ M') ≤ 3 := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun k : ↥(M ⊓ M') => (⟨⟨k.1, hKM k.2⟩, hM'ab x hxM' k (hKM' k.2),
          hM'ab y hyM' k (hKM' k.2)⟩ :
          {m : ↥M // x * m = m * x ∧ y * m = m * y})) ?_) (hF2 x hxS hxM y hyS hyM hy2' hy3')
      intro a b hab
      exact Subtype.ext (congrArg
        (fun t : {m : ↥M // x * m = m * x ∧ y * m = m * y} => (t.1 : G)) hab)
    omega

end CFSG.Quasithin.H13.U43
