module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Coll

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H] {c w : H}

theorem P1Rel.cr_C_WW (hww : c * (w * w) = w * w * c) : c * (w * w) = w * (w * c) := by
  rw [hww, mul_assoc]

theorem P1Rel.cr_C_WW_t (hww : c * (w * w) = w * w * c) (r : H) :
    c * (w * (w * r)) = w * (w * (c * r)) := by
  have h := congrArg (· * r) hww
  simpa only [mul_assoc] using h

macro "collc0 " hR:term:max hC:term:max : tactic =>
  `(tactic| simp only [
    mul_assoc, mul_inv_rev, inv_inv, mul_one, one_mul, pow_two, pow_zero, pow_one, inv_one,
    fcomm, P1Rel.y_inv $hR, P1Rel.z_inv $hR, P1Rel.za_inv $hR, P1Rel.w_inv $hR,
    P1Rel.y_four $hR, P1Rel.z_four $hR, P1Rel.cr_W4 $hR, P1Rel.cr_W4_t $hR,
    P1Rel.cr_Y0_Y0 $hR, P1Rel.cr_Y0_Y0_t $hR, P1Rel.cr_Z0_Z0 $hR, P1Rel.cr_Z0_Z0_t $hR,
    P1Rel.cr_Y1_Y1 $hR, P1Rel.cr_Y1_Y1_t $hR, P1Rel.cr_Z1_Z1 $hR, P1Rel.cr_Z1_Z1_t $hR,
    P1Rel.cr_Y2_Y2 $hR, P1Rel.cr_Y2_Y2_t $hR, P1Rel.cr_Z2_Z2 $hR, P1Rel.cr_Z2_Z2_t $hR,
    P1Rel.cr_Y3_Y3 $hR, P1Rel.cr_Y3_Y3_t $hR, P1Rel.cr_Z3_Z3 $hR, P1Rel.cr_Z3_Z3_t $hR,
    P1Rel.cr_A_A $hR, P1Rel.cr_A_A_t $hR, P1Rel.cr_Y0_W $hR, P1Rel.cr_Y0_W_t $hR,
    P1Rel.cr_Z0_W $hR, P1Rel.cr_Z0_W_t $hR, P1Rel.cr_Y1_W $hR, P1Rel.cr_Y1_W_t $hR,
    P1Rel.cr_Z1_W $hR, P1Rel.cr_Z1_W_t $hR, P1Rel.cr_Y2_W $hR, P1Rel.cr_Y2_W_t $hR,
    P1Rel.cr_Z2_W $hR, P1Rel.cr_Z2_W_t $hR, P1Rel.cr_Y3_W $hR, P1Rel.cr_Y3_W_t $hR,
    P1Rel.cr_Z3_W $hR, P1Rel.cr_Z3_W_t $hR, P1Rel.cr_Y1_Y0 $hR, P1Rel.cr_Y1_Y0_t $hR,
    P1Rel.cr_Y2_Y0 $hR, P1Rel.cr_Y2_Y0_t $hR, P1Rel.cr_Y2_Y1 $hR, P1Rel.cr_Y2_Y1_t $hR,
    P1Rel.cr_Y3_Y0 $hR, P1Rel.cr_Y3_Y0_t $hR, P1Rel.cr_Y3_Y1 $hR, P1Rel.cr_Y3_Y1_t $hR,
    P1Rel.cr_Y3_Y2 $hR, P1Rel.cr_Y3_Y2_t $hR, P1Rel.cr_A_W $hR, P1Rel.cr_A_W_t $hR,
    P1Rel.cr_A_Y0 $hR, P1Rel.cr_A_Y0_t $hR, P1Rel.cr_A_Z0 $hR, P1Rel.cr_A_Z0_t $hR,
    P1Rel.cr_A_Y1 $hR, P1Rel.cr_A_Y1_t $hR, P1Rel.cr_A_Z1 $hR, P1Rel.cr_A_Z1_t $hR,
    P1Rel.cr_A_Y2 $hR, P1Rel.cr_A_Y2_t $hR, P1Rel.cr_A_Z2 $hR, P1Rel.cr_A_Z2_t $hR,
    P1Rel.cr_A_Y3 $hR, P1Rel.cr_A_Y3_t $hR, P1Rel.cr_A_Z3 $hR, P1Rel.cr_A_Z3_t $hR,
    P1Rel.cr_Z0_Y0 $hR, P1Rel.cr_Z0_Y0_t $hR, P1Rel.cr_Z0_Y1 $hR, P1Rel.cr_Z0_Y1_t $hR,
    P1Rel.cr_Z0_Y2 $hR, P1Rel.cr_Z0_Y2_t $hR, P1Rel.cr_Z0_Y3 $hR, P1Rel.cr_Z0_Y3_t $hR,
    P1Rel.cr_Z1_Y0 $hR, P1Rel.cr_Z1_Y0_t $hR, P1Rel.cr_Z1_Y1 $hR, P1Rel.cr_Z1_Y1_t $hR,
    P1Rel.cr_Z1_Y2 $hR, P1Rel.cr_Z1_Y2_t $hR, P1Rel.cr_Z1_Y3 $hR, P1Rel.cr_Z1_Y3_t $hR,
    P1Rel.cr_Z2_Y0 $hR, P1Rel.cr_Z2_Y0_t $hR, P1Rel.cr_Z2_Y1 $hR, P1Rel.cr_Z2_Y1_t $hR,
    P1Rel.cr_Z2_Y2 $hR, P1Rel.cr_Z2_Y2_t $hR, P1Rel.cr_Z2_Y3 $hR, P1Rel.cr_Z2_Y3_t $hR,
    P1Rel.cr_Z3_Y0 $hR, P1Rel.cr_Z3_Y0_t $hR, P1Rel.cr_Z3_Y1 $hR, P1Rel.cr_Z3_Y1_t $hR,
    P1Rel.cr_Z3_Y2 $hR, P1Rel.cr_Z3_Y2_t $hR, P1Rel.cr_Z3_Y3 $hR, P1Rel.cr_Z3_Y3_t $hR,
    P1Rel.cr_Z1_Z0 $hR, P1Rel.cr_Z1_Z0_t $hR, P1Rel.cr_Z2_Z0 $hR, P1Rel.cr_Z2_Z0_t $hR,
    P1Rel.cr_Z2_Z1 $hR, P1Rel.cr_Z2_Z1_t $hR, P1Rel.cr_Z3_Z0 $hR, P1Rel.cr_Z3_Z0_t $hR,
    P1Rel.cr_Z3_Z1 $hR, P1Rel.cr_Z3_Z1_t $hR, P1Rel.cr_Z3_Z2 $hR, P1Rel.cr_Z3_Z2_t $hR,
    P1Rel.c_inv $hR $hC, P1Rel.cr_C_C $hR $hC, P1Rel.cr_C_C_t $hR $hC, P1Rel.cr_C_Y0 $hR $hC,
    P1Rel.cr_C_Y0_t $hR $hC, P1Rel.cr_C_Y1 $hR $hC, P1Rel.cr_C_Y1_t $hR $hC,
    P1Rel.cr_C_Y2 $hR $hC, P1Rel.cr_C_Y2_t $hR $hC, P1Rel.cr_C_Y3 $hR $hC,
    P1Rel.cr_C_Y3_t $hR $hC, P1Rel.cr_A_C $hR $hC, P1Rel.cr_A_C_t $hR $hC,
    P1Rel.cr_Z0_C $hR $hC, P1Rel.cr_Z0_C_t $hR $hC, P1Rel.cr_Z1_C $hR $hC,
    P1Rel.cr_Z1_C_t $hR $hC, P1Rel.cr_Z2_C $hR $hC, P1Rel.cr_Z2_C_t $hR $hC,
    P1Rel.cr_Z3_C $hR $hC, P1Rel.cr_Z3_C_t $hR $hC])

macro "collc2 " hR:term:max hC:term:max hww:term:max : tactic =>
  `(tactic| simp only [
    mul_assoc, mul_inv_rev, inv_inv, mul_one, one_mul, pow_two, pow_zero, pow_one, inv_one,
    fcomm, P1Rel.y_inv $hR, P1Rel.z_inv $hR, P1Rel.za_inv $hR, P1Rel.w_inv $hR,
    P1Rel.y_four $hR, P1Rel.z_four $hR, P1Rel.cr_W4 $hR, P1Rel.cr_W4_t $hR,
    P1Rel.cr_Y0_Y0 $hR, P1Rel.cr_Y0_Y0_t $hR, P1Rel.cr_Z0_Z0 $hR, P1Rel.cr_Z0_Z0_t $hR,
    P1Rel.cr_Y1_Y1 $hR, P1Rel.cr_Y1_Y1_t $hR, P1Rel.cr_Z1_Z1 $hR, P1Rel.cr_Z1_Z1_t $hR,
    P1Rel.cr_Y2_Y2 $hR, P1Rel.cr_Y2_Y2_t $hR, P1Rel.cr_Z2_Z2 $hR, P1Rel.cr_Z2_Z2_t $hR,
    P1Rel.cr_Y3_Y3 $hR, P1Rel.cr_Y3_Y3_t $hR, P1Rel.cr_Z3_Z3 $hR, P1Rel.cr_Z3_Z3_t $hR,
    P1Rel.cr_A_A $hR, P1Rel.cr_A_A_t $hR, P1Rel.cr_Y0_W $hR, P1Rel.cr_Y0_W_t $hR,
    P1Rel.cr_Z0_W $hR, P1Rel.cr_Z0_W_t $hR, P1Rel.cr_Y1_W $hR, P1Rel.cr_Y1_W_t $hR,
    P1Rel.cr_Z1_W $hR, P1Rel.cr_Z1_W_t $hR, P1Rel.cr_Y2_W $hR, P1Rel.cr_Y2_W_t $hR,
    P1Rel.cr_Z2_W $hR, P1Rel.cr_Z2_W_t $hR, P1Rel.cr_Y3_W $hR, P1Rel.cr_Y3_W_t $hR,
    P1Rel.cr_Z3_W $hR, P1Rel.cr_Z3_W_t $hR, P1Rel.cr_Y1_Y0 $hR, P1Rel.cr_Y1_Y0_t $hR,
    P1Rel.cr_Y2_Y0 $hR, P1Rel.cr_Y2_Y0_t $hR, P1Rel.cr_Y2_Y1 $hR, P1Rel.cr_Y2_Y1_t $hR,
    P1Rel.cr_Y3_Y0 $hR, P1Rel.cr_Y3_Y0_t $hR, P1Rel.cr_Y3_Y1 $hR, P1Rel.cr_Y3_Y1_t $hR,
    P1Rel.cr_Y3_Y2 $hR, P1Rel.cr_Y3_Y2_t $hR, P1Rel.cr_A_W $hR, P1Rel.cr_A_W_t $hR,
    P1Rel.cr_A_Y0 $hR, P1Rel.cr_A_Y0_t $hR, P1Rel.cr_A_Z0 $hR, P1Rel.cr_A_Z0_t $hR,
    P1Rel.cr_A_Y1 $hR, P1Rel.cr_A_Y1_t $hR, P1Rel.cr_A_Z1 $hR, P1Rel.cr_A_Z1_t $hR,
    P1Rel.cr_A_Y2 $hR, P1Rel.cr_A_Y2_t $hR, P1Rel.cr_A_Z2 $hR, P1Rel.cr_A_Z2_t $hR,
    P1Rel.cr_A_Y3 $hR, P1Rel.cr_A_Y3_t $hR, P1Rel.cr_A_Z3 $hR, P1Rel.cr_A_Z3_t $hR,
    P1Rel.cr_Z0_Y0 $hR, P1Rel.cr_Z0_Y0_t $hR, P1Rel.cr_Z0_Y1 $hR, P1Rel.cr_Z0_Y1_t $hR,
    P1Rel.cr_Z0_Y2 $hR, P1Rel.cr_Z0_Y2_t $hR, P1Rel.cr_Z0_Y3 $hR, P1Rel.cr_Z0_Y3_t $hR,
    P1Rel.cr_Z1_Y0 $hR, P1Rel.cr_Z1_Y0_t $hR, P1Rel.cr_Z1_Y1 $hR, P1Rel.cr_Z1_Y1_t $hR,
    P1Rel.cr_Z1_Y2 $hR, P1Rel.cr_Z1_Y2_t $hR, P1Rel.cr_Z1_Y3 $hR, P1Rel.cr_Z1_Y3_t $hR,
    P1Rel.cr_Z2_Y0 $hR, P1Rel.cr_Z2_Y0_t $hR, P1Rel.cr_Z2_Y1 $hR, P1Rel.cr_Z2_Y1_t $hR,
    P1Rel.cr_Z2_Y2 $hR, P1Rel.cr_Z2_Y2_t $hR, P1Rel.cr_Z2_Y3 $hR, P1Rel.cr_Z2_Y3_t $hR,
    P1Rel.cr_Z3_Y0 $hR, P1Rel.cr_Z3_Y0_t $hR, P1Rel.cr_Z3_Y1 $hR, P1Rel.cr_Z3_Y1_t $hR,
    P1Rel.cr_Z3_Y2 $hR, P1Rel.cr_Z3_Y2_t $hR, P1Rel.cr_Z3_Y3 $hR, P1Rel.cr_Z3_Y3_t $hR,
    P1Rel.cr_Z1_Z0 $hR, P1Rel.cr_Z1_Z0_t $hR, P1Rel.cr_Z2_Z0 $hR, P1Rel.cr_Z2_Z0_t $hR,
    P1Rel.cr_Z2_Z1 $hR, P1Rel.cr_Z2_Z1_t $hR, P1Rel.cr_Z3_Z0 $hR, P1Rel.cr_Z3_Z0_t $hR,
    P1Rel.cr_Z3_Z1 $hR, P1Rel.cr_Z3_Z1_t $hR, P1Rel.cr_Z3_Z2 $hR, P1Rel.cr_Z3_Z2_t $hR,
    P1Rel.c_inv $hR $hC, P1Rel.cr_C_C $hR $hC, P1Rel.cr_C_C_t $hR $hC, P1Rel.cr_C_Y0 $hR $hC,
    P1Rel.cr_C_Y0_t $hR $hC, P1Rel.cr_C_Y1 $hR $hC, P1Rel.cr_C_Y1_t $hR $hC,
    P1Rel.cr_C_Y2 $hR $hC, P1Rel.cr_C_Y2_t $hR $hC, P1Rel.cr_C_Y3 $hR $hC,
    P1Rel.cr_C_Y3_t $hR $hC, P1Rel.cr_A_C $hR $hC, P1Rel.cr_A_C_t $hR $hC,
    P1Rel.cr_Z0_C $hR $hC, P1Rel.cr_Z0_C_t $hR $hC, P1Rel.cr_Z1_C $hR $hC,
    P1Rel.cr_Z1_C_t $hR $hC, P1Rel.cr_Z2_C $hR $hC, P1Rel.cr_Z2_C_t $hR $hC,
    P1Rel.cr_Z3_C $hR $hC, P1Rel.cr_Z3_C_t $hR $hC, P1Rel.cr_C_WW $hww, P1Rel.cr_C_WW_t $hww])

end CFSG.Quasithin.Fan86
