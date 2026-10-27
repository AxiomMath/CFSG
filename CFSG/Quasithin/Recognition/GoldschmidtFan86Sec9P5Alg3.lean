module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Alg3b

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H]

theorem P5Ids.p3_conj_pow (x a : H) (n : ℕ) : x⁻¹ * a ^ n * x = (x⁻¹ * a * x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, ← ih]; group

variable {x w za : H} {y z : Fin 5 → H} {xb t w2 ub : H} {zm ym za' : Fin 3 → H} {e₁ e₂ : ℕ}
  (h : P5Ids w za y z xb t w2 ub zm ym za' e₁ e₂) (hR : P1Rel x w za y z)

include h hR

namespace P5Ids

theorem p3_dual :
    t⁻¹ * w * t = (xb⁻¹ * w2 * xb) * (zm 1 * ym 1 * ub * za' 0 * za' 1 ^ e₁) := by
  have key : xb⁻¹ * (t⁻¹ * w2 * t) * xb = t⁻¹ * w * t := by
    rw [← h.xw]; exact conj_dual h.xb_t w
  rw [h.p3_w2t hR] at key
  rw [← key]
  simp only [conj_mul', p3_conj_pow, h.xz, h.xy, h.xa, h.xub, Fin.reduceAdd]
  simp only [mul_assoc]

theorem p3_w2x :
    xb⁻¹ * w2 * xb = w * w2 * zm 2 * zm 0 * ym 2 * ub * za' 0 ^ (e₁ + e₂ + 1) := by
  have hd := h.p3_dual hR
  rw [h.p3_w1t hR] at hd
  calc xb⁻¹ * w2 * xb
      = (w * w2 * zm 2 * zm 1 * zm 0 * ym 0 * ub * za' 0 * za' 2 ^ e₁ * za' 0 ^ e₂) *
          (zm 1 * ym 1 * ub * za' 0 * za' 1 ^ e₁)⁻¹ := eq_mul_inv_of_mul_eq hd.symm
    _ = (w * w2 * zm 2) * ((zm 1 * zm 0 * ym 0 * ub * za' 0 * za' 2 ^ e₁ * za' 0 ^ e₂) *
          (zm 1 * ym 1 * ub * za' 0 * za' 1 ^ e₁)⁻¹) := by simp only [mul_assoc]
    _ = (w * w2 * zm 2) * (zm 0 * ym 2 * ub * za' 0 ^ (e₁ + e₂ + 1)) := by rw [h.p3_aux hR]
    _ = w * w2 * zm 2 * zm 0 * ym 2 * ub * za' 0 ^ (e₁ + e₂ + 1) := by simp only [mul_assoc]

theorem p2Rel913 : P2Rel913 e₁ e₂ xb t w w2 ub zm ym za' where
  w1x := h.xw
  w2x := h.p3_w2x hR
  w1t := h.p3_w1t hR
  w2t := h.p3_w2t hR
  w1w2 := h.p3_w1w2 hR

theorem p3_conj_w2x :
    w = w2 * (w * w2 * zm 2 * zm 0 * ym 2 * ub * za' 0 ^ (e₁ + e₂ + 1)) * zm 0 * zm 1 * ym 0 *
      ub * za' 1 ^ (e₁ + e₂ + 1) := by
  have h3 : xb⁻¹ * (xb⁻¹ * w2 * xb) * xb = w := by
    have h32 : xb * xb * xb = 1 := by rw [← pow_three']; exact h.xb3
    rw [← h.xw]
    calc xb⁻¹ * (xb⁻¹ * (xb⁻¹ * w * xb) * xb) * xb = (xb * xb * xb)⁻¹ * w * (xb * xb * xb) := by
          group
      _ = w := by rw [h32]; group
  have h4 : xb⁻¹ * (xb⁻¹ * w2 * xb) * xb =
      xb⁻¹ * (w * w2 * zm 2 * zm 0 * ym 2 * ub * za' 0 ^ (e₁ + e₂ + 1)) * xb := by
    rw [h.p3_w2x hR]
  refine h3.symm.trans (h4.trans ?_)
  simp only [conj_mul', p3_conj_pow, h.xz, h.xy, h.xa, h.xub, h.xw, Fin.reduceAdd]
  rw [h.p3_w2x hR]

theorem exp_eq (hz2 : z 2 ≠ 1) : e₁ = e₂ := by
  by_contra hne
  have h12 : e₁ + e₂ = 1 := by
    have := h.e1le
    have := h.e2le
    omega
  apply hz2
  have h3 : w = w * z 2 := (h.p3_conj_w2x hR).trans (h.p3_odd hR h12)
  exact left_eq_mul.1 h3

end P5Ids

end CFSG.Quasithin.Fan86
