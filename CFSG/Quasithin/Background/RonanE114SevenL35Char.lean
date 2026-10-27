module

public import CFSG.CharacterTheory.Wreathed.OriginalCoordinates

public section

namespace CFSG.Quasithin.RonanE114.Seven.L35

open CFSG.Wreathed

theorem vFour_eq : Original.V 4 = vSubgroup 1 := Original.V_atQuarter 1

theorem mem_vFour_iff_coord (a b : ZMod 4) (e : ZMod 2) :
    element 4 a b e ∈ Original.V 4 ↔ a - b = 0 ∨ a - b = 2 := by
  rw [vFour_eq]
  exact element_mem_v 1 a b e

theorem sq_base_iff (a b : ZMod 4) :
    (element 4 a b 0 ^ 2 = 1 ∨ element 4 a b 0 ^ 2 = element 4 2 2 0) ↔
      (a - b = 0 ∨ a - b = 2) := by
  rw [element_base_pow, ← element_zero 4, element_eq_iff, element_eq_iff]
  revert a b
  decide

theorem sq_swap_iff (a b : ZMod 4) :
    (element 4 a b 1 ^ 2 = 1 ∨ element 4 a b 1 ^ 2 = element 4 2 2 0) ↔
      (a - b = 0 ∨ a - b = 2) := by
  rw [element_swap_sq, ← element_zero 4, element_eq_iff, element_eq_iff]
  revert a b
  decide

theorem mem_vFour_iff_sq (g : Wreath 4) :
    g ∈ Original.V 4 ↔ g ^ 2 = 1 ∨ g ^ 2 = element 4 2 2 0 := by
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv 4).symm.surjective g
  change element 4 a b e ∈ Original.V 4 ↔
    element 4 a b e ^ 2 = 1 ∨ element 4 a b e ^ 2 = element 4 2 2 0
  rw [mem_vFour_iff_coord]
  rcases swap_exponent_cases e with rfl | rfl
  · exact (sq_base_iff a b).symm
  · exact (sq_swap_iff a b).symm

theorem alpha_sq_eq_one : element 4 2 2 0 ^ 2 = 1 := by
  rw [element_base_pow, ← element_zero 4, element_eq_iff]
  decide

theorem alpha_ne_one : element 4 2 2 0 ≠ 1 := by
  rw [ne_eq, ← element_zero 4, element_eq_iff]
  decide

theorem eq_two_of_two_smul (c : ZMod 4) (h : (2 : ℕ) • c = 0) (hc : c ≠ 0) : c = 2 := by
  have key : ∀ x : ZMod 4, (2 : ℕ) • x = 0 → x ≠ 0 → x = 2 := by decide
  exact key c h hc

theorem alpha_fixed (φ : Wreath 4 ≃* Wreath 4) :
    φ (element 4 2 2 0) = element 4 2 2 0 := by
  have hz : element 4 2 2 0 ∈ Subgroup.center (Wreath 4) :=
    (element_mem_center_iff 4 (by norm_num) 2 2 0).mpr ⟨rfl, rfl⟩
  have hzφ : φ (element 4 2 2 0) ∈ Subgroup.center (Wreath 4) :=
    Subgroup.mem_comap.mp (((SetLike.ext_iff.mp
      ((Subgroup.centerCharacteristic (G := Wreath 4)).fixed φ)) (element 4 2 2 0)).mpr hz)
  obtain ⟨⟨c, d, f⟩, hc⟩ := (coordinateEquiv 4).symm.surjective (φ (element 4 2 2 0))
  change element 4 c d f = φ (element 4 2 2 0) at hc
  rw [← hc] at hzφ
  obtain ⟨hf, hcd⟩ := (element_mem_center_iff 4 (by norm_num) c d f).mp hzφ
  rw [hf, ← hcd] at hc
  have hsq : element 4 c c 0 ^ 2 = 1 := by
    rw [hc, ← map_pow φ, alpha_sq_eq_one, map_one]
  have hne : element 4 c c 0 ≠ 1 := by
    intro h
    have h1 : φ (element 4 2 2 0) = φ 1 := by
      rw [map_one, ← hc, h]
    exact alpha_ne_one (φ.injective h1)
  have hc0 : c ≠ 0 := by
    intro h0
    subst h0
    exact hne (element_zero 4)
  have htwo : (2 : ℕ) • c = 0 := by
    rw [element_base_pow, ← element_zero 4, element_eq_iff] at hsq
    exact hsq.1
  have hc2 : c = 2 := eq_two_of_two_smul c htwo hc0
  subst hc2
  exact hc.symm

theorem original_V_characteristic_four : (Original.V (2 ^ 2)).Characteristic := by
  show (Original.V 4).Characteristic
  refine Subgroup.characteristic_iff_map_le.mpr fun φ => ?_
  rintro _ ⟨g, hg, rfl⟩
  show φ g ∈ Original.V 4
  rw [mem_vFour_iff_sq, ← map_pow φ]
  rcases (mem_vFour_iff_sq g).mp hg with h | h
  · rw [h, map_one]
    exact Or.inl rfl
  · rw [h, alpha_fixed]
    exact Or.inr rfl

end CFSG.Quasithin.RonanE114.Seven.L35
