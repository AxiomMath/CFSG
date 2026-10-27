module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F98Ids

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H] {x w za c : H} {y z : Fin 5 → H} {xb t ub : H}
  {zm ym za' : Fin 3 → H}

namespace IdsBase

variable (h : IdsBase w za y z xb t ub zm ym za')

include h

theorem conj_ym_zero : xb⁻¹ * ym 0 * xb = ym 1 := by
  have := h.xy 0
  rwa [show (0 : Fin 3) + 1 = 1 from rfl] at this

theorem conj_ym_one : xb⁻¹ * ym 1 * xb = ym 2 := by
  have := h.xy 1
  rwa [show (1 : Fin 3) + 1 = 2 from rfl] at this

theorem conj_ym_two : xb⁻¹ * ym 2 * xb = ym 0 := by
  have := h.xy 2
  rwa [show (2 : Fin 3) + 1 = 0 from rfl] at this

theorem conj_za_zero : xb⁻¹ * za' 0 * xb = za' 1 := by
  have := h.xa 0
  rwa [show (0 : Fin 3) + 1 = 1 from rfl] at this

theorem conj_za_two : xb⁻¹ * za' 2 * xb = za' 0 := by
  have := h.xa 2
  rwa [show (2 : Fin 3) + 1 = 0 from rfl] at this

theorem stepA (hub : xb⁻¹ * ub * xb = ub) (h96a : w⁻¹ * ym 0 * w = ym 0 * ub * za' 0) {u : H}
    (h96c : w⁻¹ * ym 2 * w = u) {w2 : H} (hxw : xb⁻¹ * w * xb = w2) :
    w2⁻¹ * ym 2 * w2 = ym 1 * ub * za' 1 * (xb⁻¹ * u * xb) := by
  have e1 := h.conj_ym_one
  have e0 := h.conj_ym_zero
  have ea := h.conj_za_zero
  calc w2⁻¹ * ym 2 * w2 = xb⁻¹ * (w⁻¹ * ym 1 * w) * xb := by
        rw [← hxw, ← e1]
        group
    _ = xb⁻¹ * ((w⁻¹ * ym 0 * w) * (w⁻¹ * ym 2 * w)) * xb := by
        rw [h.ym1]
        group
    _ = (xb⁻¹ * ym 0 * xb) * (xb⁻¹ * ub * xb) * (xb⁻¹ * za' 0 * xb) * (xb⁻¹ * u * xb) := by
        rw [h96a, h96c]
        group
    _ = ym 1 * ub * za' 1 * (xb⁻¹ * u * xb) := by rw [e0, hub, ea]

end IdsBase

namespace E1Ids

variable (h : E1Ids w za y z xb t ub zm ym za')

include h

theorem exp_eq (hR : P1Rel x w za y z) (hub : xb⁻¹ * ub * xb = ub)
    (h96a : w⁻¹ * ym 0 * w = ym 0 * ub * za' 0) (h96c : w⁻¹ * ym 2 * w = ym 2) {w2 : H}
    (hxw : xb⁻¹ * w * xb = w2) {a a' b e : ℕ} (ha : a ≤ 1) (ha' : a' ≤ 1)
    (hw2 : w2 = y 3 * y 4 * z 3 * z 0 ^ a * z 1 ^ a' * z 2 ^ b * za ^ e) (hne : za ≠ 1) :
    a = a' := by
  have hQ : w2⁻¹ * ym 2 * w2 = ym 1 * ub * za' 1 * ym 0 := by
    rw [h.toIdsBase.stepA hub h96a h96c hxw, h.toIdsBase.conj_ym_two]
  have hX : ym 1 * ub * za' 1 * ym 0 = y 2 * z 1 * z 3 := by idc h hR
  have hc2 : z 2 * (y 2 * z 1 * z 3 * za) = (y 2 * z 1 * z 3 * za) * z 2 := by coll hR
  have hca : za * (y 2 * z 1 * z 3 * za) = (y 2 * z 1 * z 3 * za) * za := by coll hR
  have hQc : (z 2 ^ b * za ^ e) * (y 2 * z 1 * z 3 * za) =
      (y 2 * z 1 * z 3 * za) * (z 2 ^ b * za ^ e) :=
    ((Commute.pow_left (show Commute (z 2) _ from hc2) b).mul_left
      (Commute.pow_left (show Commute za _ from hca) e)).eq
  have fin : ∀ P : H, P⁻¹ * ym 2 * P = y 2 * z 1 * z 3 * za →
      w2 = P * (z 2 ^ b * za ^ e) → False := by
    intro P hBp hsplit
    have h1 := conj_tail hQc hBp
    rw [← hsplit, hQ, hX] at h1
    exact hne (eq_one_of_eq_mul h1)
  by_contra hne'
  rcases (show (a = 1 ∧ a' = 0) ∨ (a = 0 ∧ a' = 1) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine fin (y 3 * y 4 * z 3 * z 0) (by idc h hR) ?_
    rw [hw2]
    simp only [pow_one, pow_zero, mul_one, mul_assoc]
  · refine fin (y 3 * y 4 * z 3 * z 1) (by idc h hR) ?_
    rw [hw2]
    simp only [pow_one, pow_zero, mul_one, mul_assoc]

end E1Ids

namespace E0Ids

variable (h : E0Ids w za y z xb t ub zm ym za')

include h

theorem exp_eq (hR : P1Rel x w za y z) (hC : P1cRel x za c y z) (hub : xb⁻¹ * ub * xb = ub)
    (h96a : w⁻¹ * ym 0 * w = ym 0 * ub * za' 0) (h96c : w⁻¹ * ym 2 * w = ym 2 * za' 2)
    {w2 : H} (hxw : xb⁻¹ * w * xb = w2) {a a' b e : ℕ} (ha : a ≤ 1) (ha' : a' ≤ 1)
    (hw2 : w2 = y 1 * y 4 * c * z 0 ^ a * z 2 ^ b * z 3 ^ a' * za ^ e) (hne : za ≠ 1) :
    a = a' := by
  have hQ : w2⁻¹ * ym 2 * w2 = ym 1 * ub * za' 1 * (ym 0 * za' 0) := by
    rw [h.toIdsBase.stepA hub h96a h96c hxw]
    congr 1
    calc xb⁻¹ * (ym 2 * za' 2) * xb = (xb⁻¹ * ym 2 * xb) * (xb⁻¹ * za' 2 * xb) := by group
      _ = ym 0 * za' 0 := by rw [h.toIdsBase.conj_ym_two, h.toIdsBase.conj_za_two]
  have hX : ym 1 * ub * za' 1 * (ym 0 * za' 0) = y 2 := by idc0 h hR hC
  have hc2 : z 2 * (y 2 * za) = (y 2 * za) * z 2 := by coll hR
  have hca : za * (y 2 * za) = (y 2 * za) * za := by coll hR
  have hQc : (z 2 ^ b * za ^ e) * (y 2 * za) = (y 2 * za) * (z 2 ^ b * za ^ e) :=
    ((Commute.pow_left (show Commute (z 2) _ from hc2) b).mul_left
      (Commute.pow_left (show Commute za _ from hca) e)).eq
  have fin : ∀ P : H, P⁻¹ * ym 2 * P = y 2 * za → w2 = P * (z 2 ^ b * za ^ e) → False := by
    intro P hBp hsplit
    have h1 := conj_tail hQc hBp
    rw [← hsplit, hQ, hX] at h1
    exact hne (eq_one_of_eq_mul h1)
  by_contra hne'
  rcases (show (a = 1 ∧ a' = 0) ∨ (a = 0 ∧ a' = 1) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine fin (y 1 * y 4 * c * z 0) (by idc0 h hR hC) ?_
    rw [hw2]
    simp only [pow_one, pow_zero, mul_one, mul_assoc]
  · refine fin (y 1 * y 4 * c * z 3) (by idc0 h hR hC) ?_
    have hcomm : z 2 ^ b * z 3 = z 3 * z 2 ^ b :=
      ((show Commute (z 2) (z 3) from commute_of_fcomm_one (hR.zz 3 2)).pow_left b).eq
    rw [hw2]
    simp only [pow_one, pow_zero, mul_one, mul_assoc]
    rw [← mul_assoc (z 2 ^ b), hcomm]
    simp only [mul_assoc]

end E0Ids

end CFSG.Quasithin.Fan86
