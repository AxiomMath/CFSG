module

public import CFSG.Quasithin.H13.GoldschmidtQ8SqE9Odd
public import CFSG.LocalAnalysis.SteinbergBKSolvableQuaternionWitness

public section

namespace CFSG.Quasithin.H13.Q8SqE9

open QuaternionGroup Subgroup CFSG.LocalAnalysis.SteinbergBK

variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

namespace Cfg

omit [Finite G] in
theorem conj_z (h : Cfg A B) {y : G} (hy : y ∈ normalizer (A : Set G)) :
    y * h.z * y⁻¹ = h.z := by
  have hA : y * h.z * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hy _).mp h.z_mem_A
  obtain ⟨w, hw⟩ := h.exists_phiA hA
  have key : ∀ w : Q8, w * w = 1 → w ≠ 1 → w = a 2 := by decide +kernel
  have h1 : (y * h.z * y⁻¹) * (y * h.z * y⁻¹) = 1 := by
    calc _ = y * (h.z * h.z) * y⁻¹ := by group
      _ = 1 := by rw [h.z_mul_self]; group
  have h2 : y * h.z * y⁻¹ ≠ 1 := by
    intro h3
    apply h.z_ne_one
    calc h.z = y⁻¹ * (y * h.z * y⁻¹) * y := by group
      _ = 1 := by rw [h3]; group
  have hw2 : w = a 2 := key w (h.phiA_inj (by rw [map_mul, hw, h1, map_one]))
    (fun hw1 => h2 (by rw [← hw, hw1, map_one]))
  rw [← hw, hw2]
  rfl

theorem three_le_card_centralizer (h : Cfg A B) {Y : Subgroup G} (hY9 : Nat.card Y = 9)
    (hYN : ∀ y ∈ Y, y ∈ normalizer (A : Set G)) (hYodd : ∀ y ∈ Y, Odd (orderOf y)) :
    3 ≤ Nat.card ↥(Y ⊓ centralizer (A : Set G)) := by
  have hAN : A ≤ normalizer (A : Set G) := Subgroup.le_normalizer
  have hY : Y ≤ normalizer (A : Set G) := fun y hy => hYN y hy
  let P : Subgroup (normalizer (A : Set G)) := A.subgroupOf (normalizer (A : Set G))
  have hPn : P.Normal := Subgroup.normal_in_normalizer
  let e : P ≃* Q8 := (Subgroup.subgroupOfEquivOfLe hAN).trans h.eA.some
  let ρ : Y →* Equiv.Perm (cyclicOrderFourSubgroups P) :=
    (axisAction P).comp (Subgroup.inclusion hY)
  have hX3 : Nat.card (cyclicOrderFourSubgroups P) = 3 := card_cyclicOrderFourSubgroups e
  have hfin : Finite (cyclicOrderFourSubgroups P) := Nat.finite_of_card_ne_zero (by omega)
  have hperm : Nat.card (Equiv.Perm (cyclicOrderFourSubgroups P)) = 6 := by
    rw [Nat.card_perm, hX3]; rfl
  have hr1 : Nat.card ρ.range ∣ 6 := hperm ▸ Subgroup.card_subgroup_dvd_card _
  have hr2 : Nat.card ρ.range ∣ 9 := hY9 ▸ Subgroup.card_range_dvd ρ
  have hr3 : Nat.card ρ.range ∣ 3 := by
    have := Nat.dvd_gcd hr1 hr2
    simpa using this
  have hk : 3 ≤ Nat.card ρ.ker := by
    have h1 := Subgroup.card_ker_mul_card_range ρ
    rw [hY9] at h1
    have hle : Nat.card ρ.range ≤ 3 := Nat.le_of_dvd (by norm_num) hr3
    have hpos : 0 < Nat.card ρ.range := Nat.card_pos
    nlinarith
  have hker : ∀ y : Y, ρ y = 1 → (y : G) ∈ centralizer (A : Set G) := by
    intro y hy
    set y' : normalizer (A : Set G) := Subgroup.inclusion hY y with hy'
    have hfix : ∀ g : normalizer (A : Set G), g ∈ P → g ^ 2 ≠ 1 →
        y' * g * y'⁻¹ = g ∨ y' * g * y'⁻¹ = g⁻¹ := by
      intro g hg hg2
      have hg4 : g ^ 4 = 1 := pow_four_of_mulEquiv_quaternionEight e hg
      have hgo : orderOf g = 4 := orderOf_eq_four_of_sq_ne_one hg4 hg2
      have hmem : zpowers g ∈ cyclicOrderFourSubgroups P :=
        ⟨zpowers_le.mpr hg, inferInstance, by rw [Nat.card_zpowers, hgo]⟩
      have h1 : ρ y ⟨zpowers g, hmem⟩ = ⟨zpowers g, hmem⟩ := by rw [hy]; rfl
      have h2 := congrArg Subtype.val h1
      change ((axisAction P y' ⟨zpowers g, hmem⟩ : cyclicOrderFourSubgroups P) : Subgroup _) =
        zpowers g at h2
      rw [axisAction_apply] at h2
      have h3 : y' * g * y'⁻¹ ∈ zpowers g := by
        rw [← h2]
        exact ⟨g, mem_zpowers g, by simp⟩
      refine eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four hgo h3 ?_
      intro h4
      apply hg2
      have h5 : y' * g ^ 2 * y'⁻¹ = 1 := by rw [← conj_pow, h4]
      simpa using h5
    have hax : ∀ m ∈ A, (y : G) * m * (y : G)⁻¹ = m ∨ (y : G) * m * (y : G)⁻¹ = m⁻¹ := by
      intro m hm
      by_cases hm2 : m * m = 1
      · have key : ∀ w : Q8, w * w = 1 → w = 1 ∨ w = a 2 := by decide +kernel
        obtain ⟨w, rfl⟩ := h.exists_phiA hm
        rcases key w (h.phiA_inj (by rw [map_mul, hm2, map_one])) with rfl | rfl
        · left; rw [map_one]; group
        · left; exact h.conj_z (hYN y y.2)
      · have hmP : (⟨m, hAN hm⟩ : normalizer (A : Set G)) ∈ P :=
          Subgroup.mem_subgroupOf.mpr hm
        have hg2 : (⟨m, hAN hm⟩ : normalizer (A : Set G)) ^ 2 ≠ 1 := by
          intro h2
          apply hm2
          have := congrArg Subtype.val h2
          simpa [pow_two] using this
        rcases hfix _ hmP hg2 with h1 | h1
        · left
          simpa [hy'] using congrArg Subtype.val h1
        · right
          simpa [hy'] using congrArg Subtype.val h1
    intro m hm
    exact (commute_of_inv_or (hYodd y y.2) hax m hm).symm
  have hsub : ρ.ker.map Y.subtype ≤ Y ⊓ centralizer (A : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y.2, hker y hy⟩
  have := h.finite_A
  calc 3 ≤ Nat.card ρ.ker := hk
    _ = Nat.card (ρ.ker.map Y.subtype) := (Subgroup.card_map_of_injective Y.subtype_injective).symm
    _ ≤ Nat.card ↥(Y ⊓ centralizer (A : Set G)) := Subgroup.card_le_of_le hsub

end Cfg

end CFSG.Quasithin.H13.Q8SqE9
