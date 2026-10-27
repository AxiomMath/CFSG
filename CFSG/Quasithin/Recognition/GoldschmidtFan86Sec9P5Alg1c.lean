module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Alg1a
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Alg1b

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H] {x w za : H} {y z : Fin 5 → H} {xb t w2 ub : H}
  {zm ym za' : Fin 3 → H} {e₁ e₂ : ℕ}
  (h : P5Ids w za y z xb t w2 ub zm ym za' e₁ e₂) (hR : P1Rel x w za y z)

include h hR

namespace P5Ids

theorem p2_zz : ∀ i j, i ≠ j → fcomm (zm i) (zm j) = ub * za' (-(i + j)) := by
  refine fin3_forall_ne ?_ ?_ ?_ ?_ ?_ ?_
  · rw [fin3_neg_add_01]; exact h.p2_zz_01 hR
  · rw [fin3_neg_add_02]; exact h.p2_zz_02 hR
  · rw [fin3_neg_add_10]; exact h.p2_zz_10 hR
  · rw [fin3_neg_add_12]; exact h.p2_zz_12 hR
  · rw [fin3_neg_add_20]; exact h.p2_zz_20 hR
  · rw [fin3_neg_add_21]; exact h.p2_zz_21 hR

theorem p2_zy : ∀ i j, i ≠ j → fcomm (zm i) (ym j) = za' i :=
  fin3_forall_ne (h.p2_zy_01 hR) (h.p2_zy_02 hR) (h.p2_zy_10 hR) (h.p2_zy_12 hR) (h.p2_zy_20 hR)
    (h.p2_zy_21 hR)

theorem p2_zaw2 : ∀ i, fcomm w2 (za' i) = 1 := by
  have hb1 : fcomm (y 3 * y 4 * z 3) (z 2) = 1 := by coll hR
  have hb2 : fcomm (y 3 * y 4 * z 3) za = 1 := by coll hR
  have hc : Commute za (z 2) := fcomm_eq_one_iff.1 (hR.cent_z 2)
  have hB1 : Commute (y 3 * y 4 * z 3) (z 2) := (fcomm_eq_one_iff.1 hb1 : Commute (z 2) _).symm
  have hB2 : Commute (y 3 * y 4 * z 3) za := (fcomm_eq_one_iff.1 hb2 : Commute za _).symm
  have hP1 : Commute (z 2 ^ e₁ * za ^ e₂) (z 2) :=
    ((Commute.refl (z 2)).pow_left e₁).mul_left (hc.pow_left e₂)
  have hP2 : Commute (z 2 ^ e₁ * za ^ e₂) za :=
    (hc.symm.pow_left e₁).mul_left ((Commute.refl za).pow_left e₂)
  have e : w2 = (y 3 * y 4 * z 3) * (z 2 ^ e₁ * za ^ e₂) := by
    rw [h.w2_eq, mul_assoc (y 3 * y 4 * z 3)]
  have hw1 : Commute w2 (z 2) := by rw [e]; exact hB1.mul_left hP1
  have hw2 : Commute w2 za := by rw [e]; exact hB2.mul_left hP2
  refine fin3_forall ?_ ?_ ?_
  · rw [h.za0]; exact fcomm_eq_one_iff.2 hw2.symm
  · rw [h.za1]; exact fcomm_eq_one_iff.2 (hw1.mul_right hw2).symm
  · rw [h.za2]; exact fcomm_eq_one_iff.2 hw1.symm

theorem p2Rel912 : P2Rel912 xb t w w2 ub zm ym za' where
  x3 := h.xb3
  t2 := by rw [h.t_eq]; exact hR.y2 0
  xt := h.xb_t
  w1sq := h.p2_w1sq hR
  zm2 := h.p2_zm2 hR
  ym2 := h.p2_ym2 hR
  za2 := h.p2_za2 hR
  ub2 := h.p2_ub2 hR
  xz := h.xz
  xy := h.xy
  xa := h.xa
  xub := h.xub
  tz := h.p2_tz hR
  ty := h.p2_ty hR
  ta := h.p2_ta hR
  tub := h.p2_tub hR
  w1z1 := h.p2_w1z1 hR
  w1z2 := h.p2_w1z2 hR
  w1z3 := h.p2_w1z3 hR
  w1y1 := h.p2_w1y1 hR
  w1y2 := h.p2_w1y2 hR
  w1ub := h.p2_w1ub hR
  zz := h.p2_zz hR
  zy := h.p2_zy hR
  zyi := h.p2_zyi hR
  zub := h.p2_zub hR
  yub := h.p2_yub hR
  yza := h.p2_yza hR
  uza := h.p2_uza hR
  zaz := h.p2_zaz hR
  zay := h.p2_zay hR
  zaw1 := h.p2_zaw1 hR
  zaw2 := h.p2_zaw2 hR
  zaza := h.p2_zaza hR
  prod_y := h.p2_prod_y hR
  prod_za := h.p2_prod_za hR

end P5Ids

end CFSG.Quasithin.Fan86
