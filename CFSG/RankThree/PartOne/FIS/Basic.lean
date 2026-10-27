module

public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions

public section

namespace CFSG.RankThree.PartOne.FIS

open CFSG.LocalAnalysis.GorensteinLyons (IsThreeTranspositions)
open CFSG.RankThree.PartTwo.Sec7

variable {G : Type*} [Group G] {D : Set G}

theorem tt_conj_mem (hD : IsThreeTranspositions D) {x : G} (hx : x ∈ D) (g : G) :
    g * x * g⁻¹ ∈ D :=
  hD.1.1 g x hx

theorem tt_mul_self (hD : IsThreeTranspositions D) {x : G} (hx : x ∈ D) : x * x = 1 :=
  mul_self_eq_one_of_orderOf_eq_two (hD.1.2.1 x hx)

theorem tt_inv_eq (hD : IsThreeTranspositions D) {x : G} (hx : x ∈ D) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (tt_mul_self hD hx)

theorem tt_ne_one (hD : IsThreeTranspositions D) {x : G} (hx : x ∈ D) : x ≠ 1 := by
  intro h
  have := hD.1.2.1 x hx
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem tt_closure_eq (hD : IsThreeTranspositions D) : Subgroup.closure D = ⊤ :=
  hD.1.2.2.1

theorem tt_cube [Finite G] (hD : IsThreeTranspositions D) {x y : G} (hx : x ∈ D) (hy : y ∈ D)
    (h : x * y ≠ y * x) : (x * y) ^ 3 = 1 := by
  have hpos : 0 < orderOf (x * y) := orderOf_pos _
  have hle : orderOf (x * y) ≤ 3 := hD.2 x hx y hy
  have h123 : orderOf (x * y) = 1 ∨ orderOf (x * y) = 2 ∨ orderOf (x * y) = 3 := by omega
  rcases h123 with h1 | h2 | h3
  · exfalso
    have h1' : x * y = 1 := orderOf_eq_one_iff.mp h1
    have hyx : y = x := by
      rw [← tt_inv_eq hD hx]
      exact eq_inv_of_mul_eq_one_right h1'
    exact h (by rw [hyx])
  · exfalso
    apply h
    have h2' : x * y * (x * y) = 1 := by rw [← pow_two, ← h2, pow_orderOf_eq_one]
    have := eq_inv_of_mul_eq_one_left h2'
    rw [mul_inv_rev, tt_inv_eq hD hx, tt_inv_eq hD hy] at this
    exact this
  · rw [← h3, pow_orderOf_eq_one]

theorem tt_braid [Finite G] (hD : IsThreeTranspositions D) {x y : G} (hx : x ∈ D) (hy : y ∈ D)
    (h : x * y ≠ y * x) : x * y * x = y * x * y := by
  have h3 := tt_cube hD hx hy h
  have h6 : x * y * x * (y * x * y) = 1 := by
    rw [← h3]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have := eq_inv_of_mul_eq_one_left h6
  rw [mul_inv_rev, mul_inv_rev, tt_inv_eq hD hx, tt_inv_eq hD hy] at this
  simpa only [mul_assoc] using this

theorem conj_comm_iff (g a b : G) :
    (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹) ↔ a * b = b * a := by
  constructor
  · intro h
    have h1 : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        _ = (g * b * g⁻¹) * (g * a * g⁻¹) := h
        _ = g * (b * a) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h1)
  · intro h
    calc (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [h]
      _ = (g * b * g⁻¹) * (g * a * g⁻¹) := by group

theorem tt_conj_eq_of_noncomm [Finite G] (hD : IsThreeTranspositions D) {a d : G}
    (ha : a ∈ D) (hd : d ∈ D)
    (h : a * d ≠ d * a) : (a * d)⁻¹ * d * (a * d) = a := by
  have hb := tt_braid hD hd ha (Ne.symm h)
  have hai := tt_inv_eq hD ha
  have hdi := tt_inv_eq hD hd
  rw [mul_inv_rev, hai, hdi]
  calc d * a * d * (a * d) = (d * a * d) * a * d := by simp only [mul_assoc]
    _ = (a * d * a) * a * d := by rw [hb]
    _ = a * d * (a * a) * d := by simp only [mul_assoc]
    _ = a := by rw [tt_mul_self hD ha, mul_one, mul_assoc, tt_mul_self hD hd, mul_one]

theorem tt_conj_eq_of_noncomm' [Finite G] (hD : IsThreeTranspositions D) {a d : G} (ha : a ∈ D)
    (hd : d ∈ D) (h : a * d ≠ d * a) : (a * d) * a * (a * d)⁻¹ = d := by
  have hb := tt_braid hD ha hd h
  have hai := tt_inv_eq hD ha
  have hdi := tt_inv_eq hD hd
  rw [mul_inv_rev, hai, hdi]
  calc a * d * a * (d * a) = (a * d * a) * d * a := by simp only [mul_assoc]
    _ = (d * a * d) * d * a := by rw [hb]
    _ = d * a * (d * d) * a := by simp only [mul_assoc]
    _ = d := by rw [tt_mul_self hD hd, mul_one, mul_assoc, tt_mul_self hD ha, mul_one]

theorem tt_sigma4_conj [Finite G] (hD : IsThreeTranspositions D) {a d v : G}
    (ha : a ∈ D) (hd : d ∈ D)
    (hv : v ∈ D) (hdv : d * v = v * d) (hda : d * a ≠ a * d) (hva : v * a ≠ a * v) :
    (a * d * v * a) * d * (a * d * v * a)⁻¹ = v := by
  have h1 : a * d * a = d * a * d := tt_braid hD ha hd (Ne.symm hda)
  have h2 : a * v * a = v * a * v := tt_braid hD ha hv (Ne.symm hva)
  have hdd := tt_mul_self hD hd
  have hvv := tt_mul_self hD hv
  have haa := tt_mul_self hD ha
  have hdvd : d * v * d = v := by
    rw [hdv, mul_assoc, hdd, mul_one]
  have hi : (a * d * v * a)⁻¹ = a * v * d * a := by
    rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, tt_inv_eq hD ha, tt_inv_eq hD hd,
      tt_inv_eq hD hv]
    simp only [mul_assoc]
  rw [hi]
  calc a * d * v * a * d * (a * v * d * a)
      = a * d * v * (a * d * a) * v * d * a := by simp only [mul_assoc]
    _ = a * d * v * (d * a * d) * v * d * a := by rw [h1]
    _ = a * (d * v * d) * a * (d * v * d) * a := by simp only [mul_assoc]
    _ = a * v * a * v * a := by rw [hdvd]
    _ = (v * a * v) * v * a := by rw [h2]
    _ = v := by
      calc (v * a * v) * v * a = v * a * (v * v) * a := by simp only [mul_assoc]
        _ = v := by rw [hvv, mul_one, mul_assoc, haa, mul_one]

end CFSG.RankThree.PartOne.FIS
