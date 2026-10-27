module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Ids

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H] {x w za : H} {y z : Fin 5 → H} {xb t w2 ub : H}
  {zm ym za' : Fin 3 → H} {e₁ e₂ : ℕ}
  (h : P5Ids w za y z xb t w2 ub zm ym za' e₁ e₂) (hR : P1Rel x w za y z)

include h hR

namespace P5Ids

theorem p3_w1t_00 (h1 : e₁ = 0) (h2 : e₂ = 0) :
    t⁻¹ * w * t =
      w * w2 * zm 2 * zm 1 * zm 0 * ym 0 * ub * za' 0 * za' 2 ^ e₁ * za' 0 ^ e₂ := by
  simp only [h.w2_eq, h1, h2]; idc h hR

theorem p3_w1t_01 (h1 : e₁ = 0) (h2 : e₂ = 1) :
    t⁻¹ * w * t =
      w * w2 * zm 2 * zm 1 * zm 0 * ym 0 * ub * za' 0 * za' 2 ^ e₁ * za' 0 ^ e₂ := by
  simp only [h.w2_eq, h1, h2]; idc h hR

theorem p3_w1t_10 (h1 : e₁ = 1) (h2 : e₂ = 0) :
    t⁻¹ * w * t =
      w * w2 * zm 2 * zm 1 * zm 0 * ym 0 * ub * za' 0 * za' 2 ^ e₁ * za' 0 ^ e₂ := by
  simp only [h.w2_eq, h1, h2]; idc h hR

theorem p3_w1t_11 (h1 : e₁ = 1) (h2 : e₂ = 1) :
    t⁻¹ * w * t =
      w * w2 * zm 2 * zm 1 * zm 0 * ym 0 * ub * za' 0 * za' 2 ^ e₁ * za' 0 ^ e₂ := by
  simp only [h.w2_eq, h1, h2]; idc h hR

theorem p3_w1t :
    t⁻¹ * w * t =
      w * w2 * zm 2 * zm 1 * zm 0 * ym 0 * ub * za' 0 * za' 2 ^ e₁ * za' 0 ^ e₂ := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h.e1le with h1 | h1 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h.e2le with h2 | h2
  exacts [h.p3_w1t_00 hR h1 h2, h.p3_w1t_01 hR h1 h2, h.p3_w1t_10 hR h1 h2,
    h.p3_w1t_11 hR h1 h2]

theorem p3_w2t_00 (h1 : e₁ = 0) (h2 : e₂ = 0) :
    t⁻¹ * w2 * t = w2 * zm 0 * ym 0 * ub * za' 2 * za' 0 ^ e₁ := by
  simp only [h.w2_eq, h1, h2]; idc h hR

theorem p3_w2t_01 (h1 : e₁ = 0) (h2 : e₂ = 1) :
    t⁻¹ * w2 * t = w2 * zm 0 * ym 0 * ub * za' 2 * za' 0 ^ e₁ := by
  simp only [h.w2_eq, h1, h2]; idc h hR

theorem p3_w2t_10 (h1 : e₁ = 1) (h2 : e₂ = 0) :
    t⁻¹ * w2 * t = w2 * zm 0 * ym 0 * ub * za' 2 * za' 0 ^ e₁ := by
  simp only [h.w2_eq, h1, h2]; idc h hR

theorem p3_w2t_11 (h1 : e₁ = 1) (h2 : e₂ = 1) :
    t⁻¹ * w2 * t = w2 * zm 0 * ym 0 * ub * za' 2 * za' 0 ^ e₁ := by
  simp only [h.w2_eq, h1, h2]; idc h hR

theorem p3_w2t :
    t⁻¹ * w2 * t = w2 * zm 0 * ym 0 * ub * za' 2 * za' 0 ^ e₁ := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h.e1le with h1 | h1 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h.e2le with h2 | h2
  exacts [h.p3_w2t_00 hR h1 h2, h.p3_w2t_01 hR h1 h2, h.p3_w2t_10 hR h1 h2,
    h.p3_w2t_11 hR h1 h2]

theorem p3_w1w2_00 (h1 : e₁ = 0) (h2 : e₂ = 0) :
    fcomm w w2 = zm 2 * zm 1 * zm 0 * ym 2 * za' 0 := by
  simp only [h.w2_eq, h1, h2]; idc h hR

theorem p3_w1w2_01 (h1 : e₁ = 0) (h2 : e₂ = 1) :
    fcomm w w2 = zm 2 * zm 1 * zm 0 * ym 2 * za' 0 := by
  simp only [h.w2_eq, h1, h2]; idc h hR

theorem p3_w1w2_10 (h1 : e₁ = 1) (h2 : e₂ = 0) :
    fcomm w w2 = zm 2 * zm 1 * zm 0 * ym 2 * za' 0 := by
  simp only [h.w2_eq, h1, h2]; idc h hR

theorem p3_w1w2_11 (h1 : e₁ = 1) (h2 : e₂ = 1) :
    fcomm w w2 = zm 2 * zm 1 * zm 0 * ym 2 * za' 0 := by
  simp only [h.w2_eq, h1, h2]; idc h hR

theorem p3_w1w2 :
    fcomm w w2 = zm 2 * zm 1 * zm 0 * ym 2 * za' 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h.e1le with h1 | h1 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h.e2le with h2 | h2
  exacts [h.p3_w1w2_00 hR h1 h2, h.p3_w1w2_01 hR h1 h2, h.p3_w1w2_10 hR h1 h2,
    h.p3_w1w2_11 hR h1 h2]

theorem p3_aux_00 (h1 : e₁ = 0) (h2 : e₂ = 0) :
    (zm 1 * zm 0 * ym 0 * ub * za' 0 * za' 2 ^ e₁ * za' 0 ^ e₂) *
      (zm 1 * ym 1 * ub * za' 0 * za' 1 ^ e₁)⁻¹ = zm 0 * ym 2 * ub * za' 0 ^ (e₁ + e₂ + 1) := by
  simp only [h1, h2, Nat.reduceAdd]; idc h hR

theorem p3_aux_01 (h1 : e₁ = 0) (h2 : e₂ = 1) :
    (zm 1 * zm 0 * ym 0 * ub * za' 0 * za' 2 ^ e₁ * za' 0 ^ e₂) *
      (zm 1 * ym 1 * ub * za' 0 * za' 1 ^ e₁)⁻¹ = zm 0 * ym 2 * ub * za' 0 ^ (e₁ + e₂ + 1) := by
  simp only [h1, h2, Nat.reduceAdd]; idc h hR

theorem p3_aux_10 (h1 : e₁ = 1) (h2 : e₂ = 0) :
    (zm 1 * zm 0 * ym 0 * ub * za' 0 * za' 2 ^ e₁ * za' 0 ^ e₂) *
      (zm 1 * ym 1 * ub * za' 0 * za' 1 ^ e₁)⁻¹ = zm 0 * ym 2 * ub * za' 0 ^ (e₁ + e₂ + 1) := by
  simp only [h1, h2, Nat.reduceAdd]; idc h hR

theorem p3_aux_11 (h1 : e₁ = 1) (h2 : e₂ = 1) :
    (zm 1 * zm 0 * ym 0 * ub * za' 0 * za' 2 ^ e₁ * za' 0 ^ e₂) *
      (zm 1 * ym 1 * ub * za' 0 * za' 1 ^ e₁)⁻¹ = zm 0 * ym 2 * ub * za' 0 ^ (e₁ + e₂ + 1) := by
  simp only [h1, h2, Nat.reduceAdd, pow_three]; idc h hR

theorem p3_aux :
    (zm 1 * zm 0 * ym 0 * ub * za' 0 * za' 2 ^ e₁ * za' 0 ^ e₂) *
      (zm 1 * ym 1 * ub * za' 0 * za' 1 ^ e₁)⁻¹ = zm 0 * ym 2 * ub * za' 0 ^ (e₁ + e₂ + 1) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h.e1le with h1 | h1 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h.e2le with h2 | h2
  exacts [h.p3_aux_00 hR h1 h2, h.p3_aux_01 hR h1 h2, h.p3_aux_10 hR h1 h2,
    h.p3_aux_11 hR h1 h2]

theorem p3_odd_01 (h1 : e₁ = 0) (h2 : e₂ = 1) :
    w2 * (w * w2 * zm 2 * zm 0 * ym 2 * ub * za' 0 ^ (e₁ + e₂ + 1)) * zm 0 * zm 1 * ym 0 * ub *
      za' 1 ^ (e₁ + e₂ + 1) = w * z 2 := by
  simp only [h.w2_eq, h1, h2, Nat.reduceAdd]; idc h hR

theorem p3_odd_10 (h1 : e₁ = 1) (h2 : e₂ = 0) :
    w2 * (w * w2 * zm 2 * zm 0 * ym 2 * ub * za' 0 ^ (e₁ + e₂ + 1)) * zm 0 * zm 1 * ym 0 * ub *
      za' 1 ^ (e₁ + e₂ + 1) = w * z 2 := by
  simp only [h.w2_eq, h1, h2, Nat.reduceAdd]; idc h hR

theorem p3_odd (h12 : e₁ + e₂ = 1) :
    w2 * (w * w2 * zm 2 * zm 0 * ym 2 * ub * za' 0 ^ (e₁ + e₂ + 1)) * zm 0 * zm 1 * ym 0 * ub *
      za' 1 ^ (e₁ + e₂ + 1) = w * z 2 := by
  have h1 := h.e1le
  have h2 := h.e2le
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h3 | h3
  · exact h.p3_odd_01 hR h3 (by omega)
  · exact h.p3_odd_10 hR h3 (by omega)

end P5Ids

end CFSG.Quasithin.Fan86
