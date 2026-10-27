module

public import CFSG.Quasithin.H13.Sp62Over
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoBase

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Quasithin SL3

namespace L32HatSL3

@[expose] def T3X1 : Finset SL3.S :=
  Finset.univ.filter fun c => InX1 c ∧ c ^ 3 = 1 ∧ c ≠ 1

@[expose] def T3X2 : Finset SL3.S :=
  Finset.univ.filter fun c => InX2 c ∧ c ^ 3 = 1 ∧ c ≠ 1

theorem T3X1_conj : ∀ c ∈ T3X1, ∀ d ∈ T3X1, ∃ g : SL3.S, InX1 g ∧ g * c * g⁻¹ = d := by
  decide +kernel

theorem T3X1_not_conj : ∀ c ∈ T3X1, ∃ g : SL3.S, ¬ InX1 (g * c * g⁻¹) := by
  decide +kernel

theorem T3X1_not_InX2 : ∀ c ∈ T3X1, ¬ InX2 c := by
  decide +kernel

theorem X1_pow_24 : ∀ y : SL3.S, InX1 y → y ^ 24 = 1 := by
  decide +kernel

theorem T3X2_conj : ∀ c ∈ T3X2, ∀ d ∈ T3X2, ∃ g : SL3.S, InX2 g ∧ g * c * g⁻¹ = d := by
  decide +kernel

theorem T3X2_not_conj : ∀ c ∈ T3X2, ∃ g : SL3.S, ¬ InX2 (g * c * g⁻¹) := by
  decide +kernel

theorem T3X2_not_InX1 : ∀ c ∈ T3X2, ¬ InX1 c := by
  decide +kernel

theorem X2_pow_24 : ∀ y : SL3.S, InX2 y → y ^ 24 = 1 := by
  decide +kernel

theorem pow_three_eq_one_of_odd {y : SL3.S} (h : y ^ 24 = 1) (ho : Odd (orderOf y)) :
    y ^ 3 = 1 := by
  have hd : orderOf y ∣ 8 * 3 := orderOf_dvd_of_pow_eq_one h
  have hc : Nat.Coprime (orderOf y) 8 := Nat.Coprime.pow_right 3 ho.coprime_two_right
  exact orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_left hd)

theorem oTwoUpper_mono {A B : Subgroup SL3.S} (h : A ≤ B) : oTwoUpper A ≤ oTwoUpper B :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem exists_odd_ne_one {Y : Subgroup SL3.S} (hO : Y ≤ oTwoUpper Y) (hY : Y ≠ ⊥) :
    ∃ y ∈ Y, y ≠ 1 ∧ Odd (orderOf y) := by
  by_contra h
  push_neg at h
  apply hY
  have hle : oTwoUpper Y ≤ ⊥ := by
    refine (Subgroup.closure_le ⊥).mpr fun x hx => ?_
    rw [SetLike.mem_coe, Subgroup.mem_bot]
    by_contra hx1
    exact h x hx.1 hx1 hx.2
  exact le_bot_iff.mp (hO.trans hle)

theorem fA4_X1 {Y : Subgroup SL3.S} (hYX : Y ≤ X1) (hP : P0 ≤ Subgroup.normalizer (Y : Set SL3.S))
    (hO : Y ≤ oTwoUpper Y) (hY : Y ≠ ⊥) : Y = oTwoUpper X1 := by
  obtain ⟨y, hyY, hy1, hyo⟩ := exists_odd_ne_one hO hY
  have hy3 : y ^ 3 = 1 := pow_three_eq_one_of_odd (X1_pow_24 y (hYX hyY)) hyo
  have hyT : y ∈ T3X1 := by
    simp only [T3X1, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hYX hyY, hy3, hy1⟩
  have hYN : Y ≤ Subgroup.normalizer (Y : Set SL3.S) := Subgroup.le_normalizer
  rcases overgroups_SL3 (Subgroup.normalizer (Y : Set SL3.S)) hP with hN | hN | hN | hN
  ·
    exfalso
    have hYX2 : Y ≤ X2 := (hN ▸ hYN).trans (inf_le_right : X1 ⊓ X2 ≤ X2)
    exact T3X1_not_InX2 y hyT (hYX2 hyY)
  ·
    have hX1N : ∀ g ∈ X1, ∀ z ∈ Y, g * z * g⁻¹ ∈ Y := fun g hg z hz =>
      (Subgroup.mem_normalizer_iff.mp (hN ▸ hg : g ∈ Subgroup.normalizer (Y : Set SL3.S)) z).mp hz
    have hT3 : ∀ d ∈ T3X1, d ∈ Y := by
      intro d hd
      obtain ⟨g, hg, hgd⟩ := T3X1_conj y hyT d hd
      rw [← hgd]
      exact hX1N g hg y hyY
    apply le_antisymm
    · exact hO.trans (oTwoUpper_mono hYX)
    · refine (Subgroup.closure_le Y).mpr fun x hx => ?_
      by_cases hx1 : x = 1
      · rw [hx1]
        exact Y.one_mem
      · have hx3 : x ^ 3 = 1 := pow_three_eq_one_of_odd (X1_pow_24 x hx.1) hx.2
        have hxT : x ∈ T3X1 := by
          simp only [T3X1, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hx.1, hx3, hx1⟩
        exact hT3 x hxT
  ·
    exfalso
    have hYX2 : Y ≤ X2 := hN ▸ hYN
    exact T3X1_not_InX2 y hyT (hYX2 hyY)
  ·
    exfalso
    obtain ⟨g, hg⟩ := T3X1_not_conj y hyT
    have hgN : g ∈ Subgroup.normalizer (Y : Set SL3.S) := by
      rw [hN]
      exact Subgroup.mem_top g
    have hgy : g * y * g⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hgN y).mp hyY
    exact hg (hYX hgy)

theorem fA4_X2 {Y : Subgroup SL3.S} (hYX : Y ≤ X2) (hP : P0 ≤ Subgroup.normalizer (Y : Set SL3.S))
    (hO : Y ≤ oTwoUpper Y) (hY : Y ≠ ⊥) : Y = oTwoUpper X2 := by
  obtain ⟨y, hyY, hy1, hyo⟩ := exists_odd_ne_one hO hY
  have hy3 : y ^ 3 = 1 := pow_three_eq_one_of_odd (X2_pow_24 y (hYX hyY)) hyo
  have hyT : y ∈ T3X2 := by
    simp only [T3X2, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hYX hyY, hy3, hy1⟩
  have hYN : Y ≤ Subgroup.normalizer (Y : Set SL3.S) := Subgroup.le_normalizer
  rcases overgroups_SL3 (Subgroup.normalizer (Y : Set SL3.S)) hP with hN | hN | hN | hN
  ·
    exfalso
    have hYX1 : Y ≤ X1 := (hN ▸ hYN).trans (inf_le_left : X1 ⊓ X2 ≤ X1)
    exact T3X2_not_InX1 y hyT (hYX1 hyY)
  ·
    exfalso
    have hYX1 : Y ≤ X1 := hN ▸ hYN
    exact T3X2_not_InX1 y hyT (hYX1 hyY)
  ·
    have hX2N : ∀ g ∈ X2, ∀ z ∈ Y, g * z * g⁻¹ ∈ Y := fun g hg z hz =>
      (Subgroup.mem_normalizer_iff.mp (hN ▸ hg : g ∈ Subgroup.normalizer (Y : Set SL3.S)) z).mp hz
    have hT3 : ∀ d ∈ T3X2, d ∈ Y := by
      intro d hd
      obtain ⟨g, hg, hgd⟩ := T3X2_conj y hyT d hd
      rw [← hgd]
      exact hX2N g hg y hyY
    apply le_antisymm
    · exact hO.trans (oTwoUpper_mono hYX)
    · refine (Subgroup.closure_le Y).mpr fun x hx => ?_
      by_cases hx1 : x = 1
      · rw [hx1]
        exact Y.one_mem
      · have hx3 : x ^ 3 = 1 := pow_three_eq_one_of_odd (X2_pow_24 x hx.1) hx.2
        have hxT : x ∈ T3X2 := by
          simp only [T3X2, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hx.1, hx3, hx1⟩
        exact hT3 x hxT
  ·
    exfalso
    obtain ⟨g, hg⟩ := T3X2_not_conj y hyT
    have hgN : g ∈ Subgroup.normalizer (Y : Set SL3.S) := by
      rw [hN]
      exact Subgroup.mem_top g
    have hgy : g * y * g⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hgN y).mp hyY
    exact hg (hYX hgy)

theorem center_S_eq_bot : Subgroup.center SL3.S = ⊥ := by
  haveI : IsSimpleGroup SL3.S := CFSG.QuasithinUnique.Vol2Native.A312L.Seven.slThree_isSimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center SL3.S) with h | h
  · exact h
  · exfalso
    have hnc : ∃ a b : SL3.S, a * b ≠ b * a := ⟨ex, ey, by decide +kernel⟩
    obtain ⟨a, b, hab⟩ := hnc
    have ha : a ∈ Subgroup.center SL3.S := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

end L32HatSL3

end CFSG.Quasithin.H13.A6
