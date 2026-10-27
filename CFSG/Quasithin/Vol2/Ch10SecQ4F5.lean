module

public import CFSG.Quasithin.Vol2.Ch10SecQ4F4

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecG.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] [Finite V] {W : Subgroup V} {Kf : Subgroup (MulAut V)}

theorem eq_one_of_odd_of_fix (hV2 : ∀ v : V, v ^ 2 = 1) (hW : Nat.card W = 4)
    (hKW : ∀ k ∈ Kf, ∀ w ∈ W, k w ∈ W) (hfaith : ∀ k ∈ Kf, (∀ w ∈ W, k w = w) → k = 1)
    {k : MulAut V} (hk : k ∈ Kf) (hodd : Odd (orderOf k)) {w₀ : V} (hw₀ : w₀ ∈ W)
    (hw₀1 : w₀ ≠ 1) (hkw₀ : k w₀ = w₀) : k = 1 := by
  have h2 : k ^ 2 = 1 :=
    hfaith _ (Kf.pow_mem hk 2) (sq_fix_of_fix hV2 hW (hKW k hk) hw₀ hw₀1 hkw₀)
  have hd : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    rw [h] at hodd
    exact (Nat.not_odd_iff_even.mpr even_two) hodd

theorem apply_ne_of_three (hV2 : ∀ v : V, v ^ 2 = 1) (hW : Nat.card W = 4)
    (hKW : ∀ k ∈ Kf, ∀ w ∈ W, k w ∈ W) (hfaith : ∀ k ∈ Kf, (∀ w ∈ W, k w = w) → k = 1)
    {y : MulAut V} (hy : y ∈ Kf) (hy3 : orderOf y = 3) {w₀ : V} (hw₀ : w₀ ∈ W)
    (hw₀1 : w₀ ≠ 1) : y w₀ ≠ w₀ := by
  intro h
  have := eq_one_of_odd_of_fix hV2 hW hKW hfaith hy (by rw [hy3]; decide) hw₀ hw₀1 h
  rw [this, orderOf_one] at hy3
  omega

theorem apply_apply_eq_mul (hV2 : ∀ v : V, v ^ 2 = 1) (hW : Nat.card W = 4)
    (hKW : ∀ k ∈ Kf, ∀ w ∈ W, k w ∈ W) (hfaith : ∀ k ∈ Kf, (∀ w ∈ W, k w = w) → k = 1)
    {y : MulAut V} (hy : y ∈ Kf) (hy3 : orderOf y = 3) {w₀ : V} (hw₀ : w₀ ∈ W)
    (hw₀1 : w₀ ≠ 1) : y (y w₀) = w₀ * y w₀ := by
  have hyw₀ : y w₀ ∈ W := hKW y hy w₀ hw₀
  have hyw₀1 : y w₀ ≠ 1 := fun h => hw₀1 (y.injective (h.trans (map_one y).symm))
  have hne := apply_ne_of_three hV2 hW hKW hfaith hy hy3 hw₀ hw₀1
  have hne' := apply_ne_of_three hV2 hW hKW hfaith hy hy3 hyw₀ hyw₀1
  have hy3' : y (y (y w₀)) = w₀ := by
    have h1 : (y ^ 3) w₀ = w₀ := by rw [← hy3, pow_orderOf_eq_one, MulAut.one_apply]
    simpa [pow_succ, MulAut.mul_apply] using h1
  rcases mem_four hV2 hW hw₀ hyw₀ hw₀1 hyw₀1 (Ne.symm hne) (hKW y hy _ hyw₀) with
    h | h | h | h
  · exact absurd (y.injective (h.trans (map_one y).symm)) hyw₀1
  · exfalso
    have h' := congrArg y h
    rw [hy3'] at h'
    exact hne h'.symm
  · exact absurd h hne'
  · exact h

theorem eq_of_odd_of_apply_eq (hV2 : ∀ v : V, v ^ 2 = 1) (hW : Nat.card W = 4)
    (hKW : ∀ k ∈ Kf, ∀ w ∈ W, k w ∈ W) (hfaith : ∀ k ∈ Kf, (∀ w ∈ W, k w = w) → k = 1)
    {y z : MulAut V} (hy : y ∈ Kf) (hy3 : orderOf y = 3) (hz : z ∈ Kf) (hodd : Odd (orderOf z))
    {w₀ : V} (hw₀ : w₀ ∈ W) (hw₀1 : w₀ ≠ 1) (hzw : z w₀ = y w₀) : z = y := by
  have hyw₀ : y w₀ ∈ W := hKW y hy w₀ hw₀
  have hyw₀1 : y w₀ ≠ 1 := fun h => hw₀1 (y.injective (h.trans (map_one y).symm))
  have hne := apply_ne_of_three hV2 hW hKW hfaith hy hy3 hw₀ hw₀1
  have hyy := apply_apply_eq_mul hV2 hW hKW hfaith hy hy3 hw₀ hw₀1
  have hzyw : z (y w₀) = y (y w₀) := by
    rcases mem_four hV2 hW hw₀ hyw₀ hw₀1 hyw₀1 (Ne.symm hne) (hKW z hz _ hyw₀) with
      h | h | h | h
    · exact absurd (z.injective (h.trans (map_one z).symm)) hyw₀1
    · exfalso
      have hz2 : (z ^ 2) w₀ = w₀ := by rw [pow_two, MulAut.mul_apply, hzw, h]
      have hodd2 : Odd (orderOf (z ^ 2)) :=
        Odd.of_dvd_nat hodd (orderOf_pow_dvd 2)
      have h1 := eq_one_of_odd_of_fix hV2 hW hKW hfaith (Kf.pow_mem hz 2) hodd2 hw₀ hw₀1 hz2
      have hd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one h1
      have hz1 : z = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hd with h' | h'
        · exact orderOf_eq_one_iff.mp h'
        · exfalso
          rw [h'] at hodd
          exact (Nat.not_odd_iff_even.mpr even_two) hodd
      rw [hz1, MulAut.one_apply] at hzw
      exact hne hzw.symm
    · exfalso
      exact hne (z.injective (h.trans hzw.symm))
    · rw [h, hyy]
  have hfix : ∀ w ∈ W, (y⁻¹ * z) w = w := by
    intro w hw
    rw [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_eq]
    rcases mem_four hV2 hW hw₀ hyw₀ hw₀1 hyw₀1 (Ne.symm hne) hw with rfl | rfl | rfl | rfl
    · rw [map_one, map_one]
    · exact hzw
    · exact hzyw
    · rw [map_mul, map_mul, hzw, hzyw]
  have h1 := hfaith _ (Kf.mul_mem (Kf.inv_mem hy) hz) hfix
  exact (inv_mul_eq_one.mp h1).symm

theorem mem_zpowers_of_odd (hV2 : ∀ v : V, v ^ 2 = 1) (hW : Nat.card W = 4)
    (hKW : ∀ k ∈ Kf, ∀ w ∈ W, k w ∈ W) (hfaith : ∀ k ∈ Kf, (∀ w ∈ W, k w = w) → k = 1)
    {y z : MulAut V} (hy : y ∈ Kf) (hy3 : orderOf y = 3) (hz : z ∈ Kf)
    (hodd : Odd (orderOf z)) : z ∈ Subgroup.zpowers y := by
  obtain ⟨w₀, hw₀, hw₀1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra hall
    push Not at hall
    have : W = ⊥ := eq_bot_iff.mpr fun w hw => hall w hw
    rw [this, Subgroup.card_bot] at hW
    omega
  have hyw₀ : y w₀ ∈ W := hKW y hy w₀ hw₀
  have hyw₀1 : y w₀ ≠ 1 := fun h => hw₀1 (y.injective (h.trans (map_one y).symm))
  have hne := apply_ne_of_three hV2 hW hKW hfaith hy hy3 hw₀ hw₀1
  rcases mem_four hV2 hW hw₀ hyw₀ hw₀1 hyw₀1 (Ne.symm hne) (hKW z hz _ hw₀) with h | h | h | h
  · exact absurd (z.injective (h.trans (map_one z).symm)) hw₀1
  · rw [eq_one_of_odd_of_fix hV2 hW hKW hfaith hz hodd hw₀ hw₀1 h]
    exact Subgroup.one_mem _
  · rw [eq_of_odd_of_apply_eq hV2 hW hKW hfaith hy hy3 hz hodd hw₀ hw₀1 h]
    exact Subgroup.mem_zpowers y
  · have hy2 : orderOf (y ^ 2) = 3 := by
      rw [orderOf_pow' _ (by norm_num), hy3]
      decide
    have hzw : z w₀ = (y ^ 2) w₀ := by
      rw [h, pow_two, MulAut.mul_apply, apply_apply_eq_mul hV2 hW hKW hfaith hy hy3 hw₀ hw₀1]
    rw [eq_of_odd_of_apply_eq hV2 hW hKW hfaith (Kf.pow_mem hy 2) hy2 hz hodd hw₀ hw₀1 hzw]
    exact Subgroup.npow_mem_zpowers y 2

end CFSG.Quasithin.Vol2.Ch10.SecG.C10E4
