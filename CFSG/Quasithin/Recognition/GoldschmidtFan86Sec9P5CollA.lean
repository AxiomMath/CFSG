module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Pres1
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H]

theorem fcomm_rule {a b d : H} (h : fcomm a b = d) : a * b = b * a * d := by
  unfold fcomm at h
  rw [← h]
  group

theorem fcomm_swap (a b : H) : fcomm b a = (fcomm a b)⁻¹ := by
  unfold fcomm
  group

theorem tail_rule {a b d : H} (h : a * b = d) (r : H) : a * (b * r) = d * r := by
  rw [← mul_assoc, h]

theorem commute_of_fcomm_one {a b : H} (h : fcomm a b = 1) : b * a = a * b := by
  have := fcomm_rule h
  rw [mul_one] at this
  exact this.symm

variable {x w za c : H} {y z : Fin 5 → H}

namespace P1Rel

theorem y_inv (hR : P1Rel x w za y z) (j : Fin 5) : (y j)⁻¹ = y j :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hR.y2 j)

theorem z_inv (hR : P1Rel x w za y z) (j : Fin 5) : (z j)⁻¹ = z j :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hR.z2 j)

theorem za_inv (hR : P1Rel x w za y z) : za⁻¹ = za :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hR.za2)

theorem cr_W4 (hR : P1Rel x w za y z) : w * (w * (w * w)) = 1 := by
  have h := hR.w4
  simp only [pow_succ, pow_zero, one_mul, mul_assoc] at h
  exact h

theorem w_inv (hR : P1Rel x w za y z) : w⁻¹ = w * (w * w) :=
  inv_eq_of_mul_eq_one_right (by simpa only [mul_assoc] using hR.cr_W4)

theorem y_four (hR : P1Rel x w za y z) : y 4 = y 3 * (y 2 * (y 1 * y 0)) := by
  have h := hR.prod_y
  unfold prodFive at h
  have : y 4 = (y 0 * y 1 * y 2 * y 3)⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [this]
  simp only [mul_inv_rev, hR.y_inv, mul_assoc]

theorem z_four (hR : P1Rel x w za y z) : z 4 = z 3 * (z 2 * (z 1 * z 0)) := by
  have h := hR.prod_z
  unfold prodFive at h
  have : z 4 = (z 0 * z 1 * z 2 * z 3)⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [this]
  simp only [mul_inv_rev, hR.z_inv, mul_assoc]

theorem cr_W4_t (hR : P1Rel x w za y z) (r : H) : w * (w * (w * (w * r))) = r := by
  simpa only [mul_assoc, one_mul] using tail_rule (hR.cr_W4) r


theorem cr_Y0_Y0 (hR : P1Rel x w za y z) :
    y 0 * y 0 = 1 := 
  (pow_two _).symm.trans (hR.y2 0)

theorem cr_Y0_Y0_t (hR : P1Rel x w za y z) (r : H) :
    y 0 * (y 0 * r) = r := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Y0_Y0 hR) r

theorem cr_Z0_Z0 (hR : P1Rel x w za y z) :
    z 0 * z 0 = 1 := 
  (pow_two _).symm.trans (hR.z2 0)

theorem cr_Z0_Z0_t (hR : P1Rel x w za y z) (r : H) :
    z 0 * (z 0 * r) = r := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z0_Z0 hR) r

theorem cr_Y1_Y1 (hR : P1Rel x w za y z) :
    y 1 * y 1 = 1 := 
  (pow_two _).symm.trans (hR.y2 1)

theorem cr_Y1_Y1_t (hR : P1Rel x w za y z) (r : H) :
    y 1 * (y 1 * r) = r := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Y1_Y1 hR) r

theorem cr_Z1_Z1 (hR : P1Rel x w za y z) :
    z 1 * z 1 = 1 := 
  (pow_two _).symm.trans (hR.z2 1)

theorem cr_Z1_Z1_t (hR : P1Rel x w za y z) (r : H) :
    z 1 * (z 1 * r) = r := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z1_Z1 hR) r

theorem cr_Y2_Y2 (hR : P1Rel x w za y z) :
    y 2 * y 2 = 1 := 
  (pow_two _).symm.trans (hR.y2 2)

theorem cr_Y2_Y2_t (hR : P1Rel x w za y z) (r : H) :
    y 2 * (y 2 * r) = r := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Y2_Y2 hR) r

theorem cr_Z2_Z2 (hR : P1Rel x w za y z) :
    z 2 * z 2 = 1 := 
  (pow_two _).symm.trans (hR.z2 2)

theorem cr_Z2_Z2_t (hR : P1Rel x w za y z) (r : H) :
    z 2 * (z 2 * r) = r := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z2_Z2 hR) r

theorem cr_Y3_Y3 (hR : P1Rel x w za y z) :
    y 3 * y 3 = 1 := 
  (pow_two _).symm.trans (hR.y2 3)

theorem cr_Y3_Y3_t (hR : P1Rel x w za y z) (r : H) :
    y 3 * (y 3 * r) = r := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Y3_Y3 hR) r

theorem cr_Z3_Z3 (hR : P1Rel x w za y z) :
    z 3 * z 3 = 1 := 
  (pow_two _).symm.trans (hR.z2 3)

theorem cr_Z3_Z3_t (hR : P1Rel x w za y z) (r : H) :
    z 3 * (z 3 * r) = r := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z3_Z3 hR) r

theorem cr_A_A (hR : P1Rel x w za y z) :
    za * za = 1 := 
  (pow_two _).symm.trans hR.za2

theorem cr_A_A_t (hR : P1Rel x w za y z) (r : H) :
    za * (za * r) = r := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_A_A hR) r

theorem cr_C_C (_hR : P1Rel x w za y z) (hC : P1cRel x za c y z) :
    c * c = za := 
  (pow_two _).symm.trans hC.c2

theorem cr_C_C_t (_hR : P1Rel x w za y z) (hC : P1cRel x za c y z) (r : H) :
    c * (c * r) = za * r := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_C_C _hR hC) r

theorem cr_Y0_W (hR : P1Rel x w za y z) :
    y 0 * w = w * y 3 := by
  have h := hR.wy 0
  have e : tauLab 0 = 3 := by decide
  rw [e] at h
  calc y 0 * w = w * (w⁻¹ * y 0 * w) := by group
    _ = w * y 3 := by rw [h]

theorem cr_Y0_W_t (hR : P1Rel x w za y z) (r : H) :
    y 0 * (w * r) = w * (y 3 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Y0_W hR) r

theorem cr_Z0_W (hR : P1Rel x w za y z) :
    z 0 * w = w * z 3 := by
  have h := hR.wz 0
  have e : tauLab 0 = 3 := by decide
  rw [e] at h
  calc z 0 * w = w * (w⁻¹ * z 0 * w) := by group
    _ = w * z 3 := by rw [h]

theorem cr_Z0_W_t (hR : P1Rel x w za y z) (r : H) :
    z 0 * (w * r) = w * (z 3 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z0_W hR) r

theorem cr_Y1_W (hR : P1Rel x w za y z) :
    y 1 * w = w * y 0 := by
  have h := hR.wy 1
  have e : tauLab 1 = 0 := by decide
  rw [e] at h
  calc y 1 * w = w * (w⁻¹ * y 1 * w) := by group
    _ = w * y 0 := by rw [h]

theorem cr_Y1_W_t (hR : P1Rel x w za y z) (r : H) :
    y 1 * (w * r) = w * (y 0 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Y1_W hR) r

theorem cr_Z1_W (hR : P1Rel x w za y z) :
    z 1 * w = w * z 0 := by
  have h := hR.wz 1
  have e : tauLab 1 = 0 := by decide
  rw [e] at h
  calc z 1 * w = w * (w⁻¹ * z 1 * w) := by group
    _ = w * z 0 := by rw [h]

theorem cr_Z1_W_t (hR : P1Rel x w za y z) (r : H) :
    z 1 * (w * r) = w * (z 0 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z1_W hR) r

theorem c_inv (hR : P1Rel x w za y z) (hC : P1cRel x za c y z) : c⁻¹ = c * za := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← mul_assoc, ← pow_two, hC.c2, ← pow_two]
  exact hR.za2

end P1Rel

end CFSG.Quasithin.Fan86
