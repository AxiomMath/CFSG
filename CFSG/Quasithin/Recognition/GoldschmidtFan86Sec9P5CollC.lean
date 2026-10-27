module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5CollA
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H] {x w za c : H} {y z : Fin 5 → H}

namespace P1Rel

theorem cr_A_Z0 (hR : P1Rel x w za y z) :
    za * z 0 = z 0 * za := 
  commute_of_fcomm_one (hR.cent_z 0)

theorem cr_A_Z0_t (hR : P1Rel x w za y z) (r : H) :
    za * (z 0 * r) = z 0 * (za * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_A_Z0 hR) r

theorem cr_A_Y1 (hR : P1Rel x w za y z) :
    za * y 1 = y 1 * za := 
  commute_of_fcomm_one (hR.cent_y 1)

theorem cr_A_Y1_t (hR : P1Rel x w za y z) (r : H) :
    za * (y 1 * r) = y 1 * (za * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_A_Y1 hR) r

theorem cr_A_Z1 (hR : P1Rel x w za y z) :
    za * z 1 = z 1 * za := 
  commute_of_fcomm_one (hR.cent_z 1)

theorem cr_A_Z1_t (hR : P1Rel x w za y z) (r : H) :
    za * (z 1 * r) = z 1 * (za * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_A_Z1 hR) r

theorem cr_A_Y2 (hR : P1Rel x w za y z) :
    za * y 2 = y 2 * za := 
  commute_of_fcomm_one (hR.cent_y 2)

theorem cr_A_Y2_t (hR : P1Rel x w za y z) (r : H) :
    za * (y 2 * r) = y 2 * (za * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_A_Y2 hR) r

theorem cr_A_Z2 (hR : P1Rel x w za y z) :
    za * z 2 = z 2 * za := 
  commute_of_fcomm_one (hR.cent_z 2)

theorem cr_A_Z2_t (hR : P1Rel x w za y z) (r : H) :
    za * (z 2 * r) = z 2 * (za * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_A_Z2 hR) r

theorem cr_A_Y3 (hR : P1Rel x w za y z) :
    za * y 3 = y 3 * za := 
  commute_of_fcomm_one (hR.cent_y 3)

theorem cr_A_Y3_t (hR : P1Rel x w za y z) (r : H) :
    za * (y 3 * r) = y 3 * (za * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_A_Y3 hR) r

theorem cr_A_Z3 (hR : P1Rel x w za y z) :
    za * z 3 = z 3 * za := 
  commute_of_fcomm_one (hR.cent_z 3)

theorem cr_A_Z3_t (hR : P1Rel x w za y z) (r : H) :
    za * (z 3 * r) = z 3 * (za * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_A_Z3 hR) r

theorem cr_A_C (_hR : P1Rel x w za y z) (hC : P1cRel x za c y z) :
    za * c = c * za := 
  commute_of_fcomm_one hC.cza

theorem cr_A_C_t (_hR : P1Rel x w za y z) (hC : P1cRel x za c y z) (r : H) :
    za * (c * r) = c * (za * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_A_C _hR hC) r

theorem cr_Z0_Y0 (hR : P1Rel x w za y z) :
    z 0 * y 0 = y 0 * z 0 := by
  have h : fcomm (z 0) (y 0) = 1 := by
    rw [fcomm_swap, hR.yz 0 0]
    simp
  simpa only [mul_assoc, mul_one] using fcomm_rule h

theorem cr_Z0_Y0_t (hR : P1Rel x w za y z) (r : H) :
    z 0 * (y 0 * r) = y 0 * (z 0 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z0_Y0 hR) r

theorem cr_Z0_Y1 (hR : P1Rel x w za y z) :
    z 0 * y 1 = y 1 * (z 0 * za) := by
  have h : fcomm (z 0) (y 1) = za := by
    rw [fcomm_swap, hR.yz 1 0]
    simp [hR.za_inv]
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_Z0_Y1_t (hR : P1Rel x w za y z) (r : H) :
    z 0 * (y 1 * r) = y 1 * (z 0 * (za * r)) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z0_Y1 hR) r

theorem cr_Z0_Y2 (hR : P1Rel x w za y z) :
    z 0 * y 2 = y 2 * (z 0 * za) := by
  have h : fcomm (z 0) (y 2) = za := by
    rw [fcomm_swap, hR.yz 2 0]
    simp [hR.za_inv]
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_Z0_Y2_t (hR : P1Rel x w za y z) (r : H) :
    z 0 * (y 2 * r) = y 2 * (z 0 * (za * r)) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z0_Y2 hR) r

theorem cr_Z0_Y3 (hR : P1Rel x w za y z) :
    z 0 * y 3 = y 3 * (z 0 * za) := by
  have h : fcomm (z 0) (y 3) = za := by
    rw [fcomm_swap, hR.yz 3 0]
    simp [hR.za_inv]
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_Z0_Y3_t (hR : P1Rel x w za y z) (r : H) :
    z 0 * (y 3 * r) = y 3 * (z 0 * (za * r)) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z0_Y3 hR) r

theorem cr_Z1_Y0 (hR : P1Rel x w za y z) :
    z 1 * y 0 = y 0 * (z 1 * za) := by
  have h : fcomm (z 1) (y 0) = za := by
    rw [fcomm_swap, hR.yz 0 1]
    simp [hR.za_inv]
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_Z1_Y0_t (hR : P1Rel x w za y z) (r : H) :
    z 1 * (y 0 * r) = y 0 * (z 1 * (za * r)) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z1_Y0 hR) r

theorem cr_Z1_Y1 (hR : P1Rel x w za y z) :
    z 1 * y 1 = y 1 * z 1 := by
  have h : fcomm (z 1) (y 1) = 1 := by
    rw [fcomm_swap, hR.yz 1 1]
    simp
  simpa only [mul_assoc, mul_one] using fcomm_rule h

theorem cr_Z1_Y1_t (hR : P1Rel x w za y z) (r : H) :
    z 1 * (y 1 * r) = y 1 * (z 1 * r) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z1_Y1 hR) r

theorem cr_Z1_Y2 (hR : P1Rel x w za y z) :
    z 1 * y 2 = y 2 * (z 1 * za) := by
  have h : fcomm (z 1) (y 2) = za := by
    rw [fcomm_swap, hR.yz 2 1]
    simp [hR.za_inv]
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_Z1_Y2_t (hR : P1Rel x w za y z) (r : H) :
    z 1 * (y 2 * r) = y 2 * (z 1 * (za * r)) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z1_Y2 hR) r

theorem cr_Z1_Y3 (hR : P1Rel x w za y z) :
    z 1 * y 3 = y 3 * (z 1 * za) := by
  have h : fcomm (z 1) (y 3) = za := by
    rw [fcomm_swap, hR.yz 3 1]
    simp [hR.za_inv]
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_Z1_Y3_t (hR : P1Rel x w za y z) (r : H) :
    z 1 * (y 3 * r) = y 3 * (z 1 * (za * r)) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z1_Y3 hR) r

theorem cr_Z2_Y0 (hR : P1Rel x w za y z) :
    z 2 * y 0 = y 0 * (z 2 * za) := by
  have h : fcomm (z 2) (y 0) = za := by
    rw [fcomm_swap, hR.yz 0 2]
    simp [hR.za_inv]
  simpa only [mul_assoc] using fcomm_rule h

theorem cr_Z2_Y0_t (hR : P1Rel x w za y z) (r : H) :
    z 2 * (y 0 * r) = y 0 * (z 2 * (za * r)) := by
  simpa only [mul_assoc, one_mul] using tail_rule (cr_Z2_Y0 hR) r

end P1Rel

end CFSG.Quasithin.Fan86
