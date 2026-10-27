module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F98Ids

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H] {x w za c : H} {y z : Fin 5 → H} {xb t ub : H}
  {zm ym za' : Fin 3 → H}

theorem E1Ids.a_zero (h : E1Ids w za y z xb t ub zm ym za') (hR : P1Rel x w za y z)
    (hub : xb⁻¹ * ub * xb = ub) {w2 : H} (hxw : xb⁻¹ * w * xb = w2) {a b e : ℕ}
    (ha : a ≤ 1)
    (hw2 : w2 = y 3 * y 4 * z 3 * z 0 ^ a * z 1 ^ a * z 2 ^ b * za ^ e)
    (hne : z 2 * za ≠ 1) : a = 0 := by
  by_contra ha0
  obtain rfl : a = 1 := by omega
  have hX : zm 1 * ym 1 * ub * za' 1 = zm 2 * y 3 * y 1 := by idc h hR
  have hBp : (y 3 * y 4 * z 3 * (z 0 * z 1))⁻¹ * zm 1 * (y 3 * y 4 * z 3 * (z 0 * z 1)) =
      zm 2 * y 3 * y 1 * (z 2 * za) := by idc h hR
  have hc2 : z 2 * (zm 2 * y 3 * y 1 * (z 2 * za)) = (zm 2 * y 3 * y 1 * (z 2 * za)) * z 2 := by
    idc h hR
  have hca : za * (zm 2 * y 3 * y 1 * (z 2 * za)) = (zm 2 * y 3 * y 1 * (z 2 * za)) * za := by
    idc h hR
  have hsplit : w2 = (y 3 * y 4 * z 3 * (z 0 * z 1)) * (z 2 ^ b * za ^ e) := by
    rw [hw2]
    simp only [pow_one, mul_assoc]
  have hQ : (z 2 ^ b * za ^ e) * (zm 2 * y 3 * y 1 * (z 2 * za)) =
      (zm 2 * y 3 * y 1 * (z 2 * za)) * (z 2 ^ b * za ^ e) :=
    ((Commute.pow_left (show Commute (z 2) _ from hc2) b).mul_left
      (Commute.pow_left (show Commute za _ from hca) e)).eq
  have h1 := conj_tail hQ hBp
  rw [← hsplit, h.toIdsBase.key hR hub hxw, hX] at h1
  exact hne (eq_one_of_eq_mul h1)

theorem E0Ids.a_zero (h : E0Ids w za y z xb t ub zm ym za') (hR : P1Rel x w za y z)
    (hC : P1cRel x za c y z) (hww : c * (w * w) = w * w * c) (hub : xb⁻¹ * ub * xb = ub)
    {w2 : H} (hxw : xb⁻¹ * w * xb = w2) {a b e : ℕ} (ha : a ≤ 1)
    (hw2 : w2 = y 1 * y 4 * c * z 0 ^ a * z 3 ^ a * z 2 ^ b * za ^ e)
    (hne : z 2 * za ≠ 1) : a = 0 := by
  by_contra ha0
  obtain rfl : a = 1 := by omega
  have hBp : (y 1 * y 4 * c * (z 0 * z 3))⁻¹ * zm 1 * (y 1 * y 4 * c * (z 0 * z 3)) =
      (zm 1 * ym 1 * ub * za' 1) * (z 2 * za) := by idc2 h hR hC hww
  have hc2 : z 2 * ((zm 1 * ym 1 * ub * za' 1) * (z 2 * za)) =
      ((zm 1 * ym 1 * ub * za' 1) * (z 2 * za)) * z 2 := by idc2 h hR hC hww
  have hca : za * ((zm 1 * ym 1 * ub * za' 1) * (z 2 * za)) =
      ((zm 1 * ym 1 * ub * za' 1) * (z 2 * za)) * za := by idc2 h hR hC hww
  have hsplit : w2 = (y 1 * y 4 * c * (z 0 * z 3)) * (z 2 ^ b * za ^ e) := by
    rw [hw2]
    simp only [pow_one, mul_assoc]
  have hQ : (z 2 ^ b * za ^ e) * ((zm 1 * ym 1 * ub * za' 1) * (z 2 * za)) =
      ((zm 1 * ym 1 * ub * za' 1) * (z 2 * za)) * (z 2 ^ b * za ^ e) :=
    ((Commute.pow_left (show Commute (z 2) _ from hc2) b).mul_left
      (Commute.pow_left (show Commute za _ from hca) e)).eq
  have h1 := conj_tail hQ hBp
  rw [← hsplit, h.toIdsBase.key hR hub hxw] at h1
  exact hne (eq_one_of_eq_mul h1)

end CFSG.Quasithin.Fan86
