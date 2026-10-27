module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5CollA

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H] {x w za c : H} {y z : Fin 5 → H}

namespace P1Rel

theorem cr_Z2_Y1 (hR : P1Rel x w za y z) :
    z 2 * y 1 = y 1 * (z 2 * za) := by
  have h : fcomm (z 2) (y 1) = za := by
    rw [fcomm_swap, hR.yz 1 2]
    simp [hR.za_inv]
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_Z2_Y1_t (hR : P1Rel x w za y z) (r : H) :
    z 2 * (y 1 * r) = y 1 * (z 2 * (za * r)) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z2_Y1 hR) r

theorem cr_Z2_Y2 (hR : P1Rel x w za y z) :
    z 2 * y 2 = y 2 * z 2 := by
  have h : fcomm (z 2) (y 2) = 1 := by
    rw [fcomm_swap, hR.yz 2 2]
    simp
  simpa only [mul_assoc, mul_one] using fcomm_rule h

theorem cr_Z2_Y2_t (hR : P1Rel x w za y z) (r : H) :
    z 2 * (y 2 * r) = y 2 * (z 2 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z2_Y2 hR) r

theorem cr_Z2_Y3 (hR : P1Rel x w za y z) :
    z 2 * y 3 = y 3 * (z 2 * za) := by
  have h : fcomm (z 2) (y 3) = za := by
    rw [fcomm_swap, hR.yz 3 2]
    simp [hR.za_inv]
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_Z2_Y3_t (hR : P1Rel x w za y z) (r : H) :
    z 2 * (y 3 * r) = y 3 * (z 2 * (za * r)) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z2_Y3 hR) r

theorem cr_Z3_Y0 (hR : P1Rel x w za y z) :
    z 3 * y 0 = y 0 * (z 3 * za) := by
  have h : fcomm (z 3) (y 0) = za := by
    rw [fcomm_swap, hR.yz 0 3]
    simp [hR.za_inv]
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_Z3_Y0_t (hR : P1Rel x w za y z) (r : H) :
    z 3 * (y 0 * r) = y 0 * (z 3 * (za * r)) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z3_Y0 hR) r

theorem cr_Z3_Y1 (hR : P1Rel x w za y z) :
    z 3 * y 1 = y 1 * (z 3 * za) := by
  have h : fcomm (z 3) (y 1) = za := by
    rw [fcomm_swap, hR.yz 1 3]
    simp [hR.za_inv]
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_Z3_Y1_t (hR : P1Rel x w za y z) (r : H) :
    z 3 * (y 1 * r) = y 1 * (z 3 * (za * r)) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z3_Y1 hR) r

theorem cr_Z3_Y2 (hR : P1Rel x w za y z) :
    z 3 * y 2 = y 2 * (z 3 * za) := by
  have h : fcomm (z 3) (y 2) = za := by
    rw [fcomm_swap, hR.yz 2 3]
    simp [hR.za_inv]
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_Z3_Y2_t (hR : P1Rel x w za y z) (r : H) :
    z 3 * (y 2 * r) = y 2 * (z 3 * (za * r)) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z3_Y2 hR) r

theorem cr_Z3_Y3 (hR : P1Rel x w za y z) :
    z 3 * y 3 = y 3 * z 3 := by
  have h : fcomm (z 3) (y 3) = 1 := by
    rw [fcomm_swap, hR.yz 3 3]
    simp
  simpa only [mul_assoc, mul_one] using fcomm_rule h

theorem cr_Z3_Y3_t (hR : P1Rel x w za y z) (r : H) :
    z 3 * (y 3 * r) = y 3 * (z 3 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z3_Y3 hR) r

theorem cr_Z1_Z0 (hR : P1Rel x w za y z) :
    z 1 * z 0 = z 0 * z 1 := by
  simpa only [mul_assoc, mul_one] using fcomm_rule (hR.zz 1 0)

theorem cr_Z1_Z0_t (hR : P1Rel x w za y z) (r : H) :
    z 1 * (z 0 * r) = z 0 * (z 1 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z1_Z0 hR) r

theorem cr_Z2_Z0 (hR : P1Rel x w za y z) :
    z 2 * z 0 = z 0 * z 2 := by
  simpa only [mul_assoc, mul_one] using fcomm_rule (hR.zz 2 0)

theorem cr_Z2_Z0_t (hR : P1Rel x w za y z) (r : H) :
    z 2 * (z 0 * r) = z 0 * (z 2 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z2_Z0 hR) r

theorem cr_Z2_Z1 (hR : P1Rel x w za y z) :
    z 2 * z 1 = z 1 * z 2 := by
  simpa only [mul_assoc, mul_one] using fcomm_rule (hR.zz 2 1)

theorem cr_Z2_Z1_t (hR : P1Rel x w za y z) (r : H) :
    z 2 * (z 1 * r) = z 1 * (z 2 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z2_Z1 hR) r

theorem cr_Z3_Z0 (hR : P1Rel x w za y z) :
    z 3 * z 0 = z 0 * z 3 := by
  simpa only [mul_assoc, mul_one] using fcomm_rule (hR.zz 3 0)

theorem cr_Z3_Z0_t (hR : P1Rel x w za y z) (r : H) :
    z 3 * (z 0 * r) = z 0 * (z 3 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z3_Z0 hR) r

theorem cr_Z3_Z1 (hR : P1Rel x w za y z) :
    z 3 * z 1 = z 1 * z 3 := by
  simpa only [mul_assoc, mul_one] using fcomm_rule (hR.zz 3 1)

theorem cr_Z3_Z1_t (hR : P1Rel x w za y z) (r : H) :
    z 3 * (z 1 * r) = z 1 * (z 3 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z3_Z1 hR) r

theorem cr_Z3_Z2 (hR : P1Rel x w za y z) :
    z 3 * z 2 = z 2 * z 3 := by
  simpa only [mul_assoc, mul_one] using fcomm_rule (hR.zz 3 2)

theorem cr_Z3_Z2_t (hR : P1Rel x w za y z) (r : H) :
    z 3 * (z 2 * r) = z 2 * (z 3 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z3_Z2 hR) r

theorem cr_Z0_C (_hR : P1Rel x w za y z) (hC : P1cRel x za c y z) :
    z 0 * c = c * z 0 := by
  simpa only [mul_assoc, mul_one] using fcomm_rule (hC.zc 0)

theorem cr_Z0_C_t (_hR : P1Rel x w za y z) (hC : P1cRel x za c y z) (r : H) :
    z 0 * (c * r) = c * (z 0 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z0_C _hR hC) r

theorem cr_Z1_C (_hR : P1Rel x w za y z) (hC : P1cRel x za c y z) :
    z 1 * c = c * z 1 := by
  simpa only [mul_assoc, mul_one] using fcomm_rule (hC.zc 1)

theorem cr_Z1_C_t (_hR : P1Rel x w za y z) (hC : P1cRel x za c y z) (r : H) :
    z 1 * (c * r) = c * (z 1 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z1_C _hR hC) r

theorem cr_Z2_C (_hR : P1Rel x w za y z) (hC : P1cRel x za c y z) :
    z 2 * c = c * z 2 := by
  simpa only [mul_assoc, mul_one] using fcomm_rule (hC.zc 2)

theorem cr_Z2_C_t (_hR : P1Rel x w za y z) (hC : P1cRel x za c y z) (r : H) :
    z 2 * (c * r) = c * (z 2 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z2_C _hR hC) r

theorem cr_Z3_C (_hR : P1Rel x w za y z) (hC : P1cRel x za c y z) :
    z 3 * c = c * z 3 := by
  simpa only [mul_assoc, mul_one] using fcomm_rule (hC.zc 3)

theorem cr_Z3_C_t (_hR : P1Rel x w za y z) (hC : P1cRel x za c y z) (r : H) :
    z 3 * (c * r) = c * (z 3 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z3_C _hR hC) r

end P1Rel

end CFSG.Quasithin.Fan86
