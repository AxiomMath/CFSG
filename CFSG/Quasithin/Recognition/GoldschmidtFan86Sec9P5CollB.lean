module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5CollA

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H] {x w za c : H} {y z : Fin 5 → H}

namespace P1Rel

theorem cr_Y2_W (hR : P1Rel x w za y z) :
    y 2 * w = w * y 2 := by
  have h := hR.wy 2
  have e : tauLab 2 = 2 := by decide
  rw [e] at h
  calc y 2 * w = w * (w⁻¹ * y 2 * w) := by group
    _ = w * y 2 := by rw [h]

theorem cr_Y2_W_t (hR : P1Rel x w za y z) (r : H) :
    y 2 * (w * r) = w * (y 2 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Y2_W hR) r

theorem cr_Z2_W (hR : P1Rel x w za y z) :
    z 2 * w = w * z 2 := by
  have h := hR.wz 2
  have e : tauLab 2 = 2 := by decide
  rw [e] at h
  calc z 2 * w = w * (w⁻¹ * z 2 * w) := by group
    _ = w * z 2 := by rw [h]

theorem cr_Z2_W_t (hR : P1Rel x w za y z) (r : H) :
    z 2 * (w * r) = w * (z 2 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z2_W hR) r

theorem cr_Y3_W (hR : P1Rel x w za y z) :
    y 3 * w = w * y 4 := by
  have h := hR.wy 3
  have e : tauLab 3 = 4 := by decide
  rw [e] at h
  calc y 3 * w = w * (w⁻¹ * y 3 * w) := by group
    _ = w * y 4 := by rw [h]

theorem cr_Y3_W_t (hR : P1Rel x w za y z) (r : H) :
    y 3 * (w * r) = w * (y 4 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Y3_W hR) r

theorem cr_Z3_W (hR : P1Rel x w za y z) :
    z 3 * w = w * z 4 := by
  have h := hR.wz 3
  have e : tauLab 3 = 4 := by decide
  rw [e] at h
  calc z 3 * w = w * (w⁻¹ * z 3 * w) := by group
    _ = w * z 4 := by rw [h]

theorem cr_Z3_W_t (hR : P1Rel x w za y z) (r : H) :
    z 3 * (w * r) = w * (z 4 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z3_W hR) r

theorem cr_C_W (_hR : P1Rel x w za y z) (_hC : P1cRel x za c y z) (hwc : fcomm w c = 1) :
    c * w = w * c := 
  commute_of_fcomm_one hwc

theorem cr_C_W_t (_hR : P1Rel x w za y z) (_hC : P1cRel x za c y z) (hwc : fcomm w c = 1) (r : H) :
    c * (w * r) = w * (c * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_C_W _hR _hC hwc) r

theorem cr_Y1_Y0 (hR : P1Rel x w za y z) :
    y 1 * y 0 = y 0 * (y 1 * (z 4 * z 2)) := by
  have h := hR.yy 1 0 (by decide)
  have e1 : kstar 1 0 = 4 := by decide
  have e2 : kstar 0 1 = 2 := by decide
  rw [e1, e2] at h
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_Y1_Y0_t (hR : P1Rel x w za y z) (r : H) :
    y 1 * (y 0 * r) = y 0 * (y 1 * (z 4 * (z 2 * r))) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Y1_Y0 hR) r

theorem cr_Y2_Y0 (hR : P1Rel x w za y z) :
    y 2 * y 0 = y 0 * (y 2 * (z 3 * z 4)) := by
  have h := hR.yy 2 0 (by decide)
  have e1 : kstar 2 0 = 3 := by decide
  have e2 : kstar 0 2 = 4 := by decide
  rw [e1, e2] at h
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_Y2_Y0_t (hR : P1Rel x w za y z) (r : H) :
    y 2 * (y 0 * r) = y 0 * (y 2 * (z 3 * (z 4 * r))) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Y2_Y0 hR) r

theorem cr_Y2_Y1 (hR : P1Rel x w za y z) :
    y 2 * y 1 = y 1 * (y 2 * (z 0 * z 3)) := by
  have h := hR.yy 2 1 (by decide)
  have e1 : kstar 2 1 = 0 := by decide
  have e2 : kstar 1 2 = 3 := by decide
  rw [e1, e2] at h
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_Y2_Y1_t (hR : P1Rel x w za y z) (r : H) :
    y 2 * (y 1 * r) = y 1 * (y 2 * (z 0 * (z 3 * r))) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Y2_Y1 hR) r

theorem cr_Y3_Y0 (hR : P1Rel x w za y z) :
    y 3 * y 0 = y 0 * (y 3 * (z 2 * z 1)) := by
  have h := hR.yy 3 0 (by decide)
  have e1 : kstar 3 0 = 2 := by decide
  have e2 : kstar 0 3 = 1 := by decide
  rw [e1, e2] at h
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_Y3_Y0_t (hR : P1Rel x w za y z) (r : H) :
    y 3 * (y 0 * r) = y 0 * (y 3 * (z 2 * (z 1 * r))) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Y3_Y0 hR) r

theorem cr_Y3_Y1 (hR : P1Rel x w za y z) :
    y 3 * y 1 = y 1 * (y 3 * (z 4 * z 0)) := by
  have h := hR.yy 3 1 (by decide)
  have e1 : kstar 3 1 = 4 := by decide
  have e2 : kstar 1 3 = 0 := by decide
  rw [e1, e2] at h
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_Y3_Y1_t (hR : P1Rel x w za y z) (r : H) :
    y 3 * (y 1 * r) = y 1 * (y 3 * (z 4 * (z 0 * r))) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Y3_Y1 hR) r

theorem cr_Y3_Y2 (hR : P1Rel x w za y z) :
    y 3 * y 2 = y 2 * (y 3 * (z 1 * z 4)) := by
  have h := hR.yy 3 2 (by decide)
  have e1 : kstar 3 2 = 1 := by decide
  have e2 : kstar 2 3 = 4 := by decide
  rw [e1, e2] at h
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_Y3_Y2_t (hR : P1Rel x w za y z) (r : H) :
    y 3 * (y 2 * r) = y 2 * (y 3 * (z 1 * (z 4 * r))) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Y3_Y2 hR) r

theorem cr_C_Y0 (hR : P1Rel x w za y z) (hC : P1cRel x za c y z) :
    c * y 0 = y 0 * (c * z 0) := by
  have h : fcomm c (y 0) = z 0 := by rw [fcomm_swap, hC.yc 0, hR.z_inv 0]
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_C_Y0_t (hR : P1Rel x w za y z) (hC : P1cRel x za c y z) (r : H) :
    c * (y 0 * r) = y 0 * (c * (z 0 * r)) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_C_Y0 hR hC) r

theorem cr_C_Y1 (hR : P1Rel x w za y z) (hC : P1cRel x za c y z) :
    c * y 1 = y 1 * (c * z 1) := by
  have h : fcomm c (y 1) = z 1 := by rw [fcomm_swap, hC.yc 1, hR.z_inv 1]
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_C_Y1_t (hR : P1Rel x w za y z) (hC : P1cRel x za c y z) (r : H) :
    c * (y 1 * r) = y 1 * (c * (z 1 * r)) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_C_Y1 hR hC) r

theorem cr_C_Y2 (hR : P1Rel x w za y z) (hC : P1cRel x za c y z) :
    c * y 2 = y 2 * (c * z 2) := by
  have h : fcomm c (y 2) = z 2 := by rw [fcomm_swap, hC.yc 2, hR.z_inv 2]
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_C_Y2_t (hR : P1Rel x w za y z) (hC : P1cRel x za c y z) (r : H) :
    c * (y 2 * r) = y 2 * (c * (z 2 * r)) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_C_Y2 hR hC) r

theorem cr_C_Y3 (hR : P1Rel x w za y z) (hC : P1cRel x za c y z) :
    c * y 3 = y 3 * (c * z 3) := by
  have h : fcomm c (y 3) = z 3 := by rw [fcomm_swap, hC.yc 3, hR.z_inv 3]
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_C_Y3_t (hR : P1Rel x w za y z) (hC : P1cRel x za c y z) (r : H) :
    c * (y 3 * r) = y 3 * (c * (z 3 * r)) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_C_Y3 hR hC) r

theorem cr_A_W (hR : P1Rel x w za y z) :
    za * w = w * za := 
  commute_of_fcomm_one hR.cent_w

theorem cr_A_W_t (hR : P1Rel x w za y z) (r : H) :
    za * (w * r) = w * (za * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_A_W hR) r

theorem cr_A_Y0 (hR : P1Rel x w za y z) :
    za * y 0 = y 0 * za := 
  commute_of_fcomm_one (hR.cent_y 0)

theorem cr_A_Y0_t (hR : P1Rel x w za y z) (r : H) :
    za * (y 0 * r) = y 0 * (za * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_A_Y0 hR) r

end P1Rel

end CFSG.Quasithin.Fan86
