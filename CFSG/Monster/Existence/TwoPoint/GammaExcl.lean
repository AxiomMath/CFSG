module

public import CFSG.Monster.Existence.InvolutionClasses
public import CFSG.Monster.Existence.TwoPoint.GammaExclAlg
public import CFSG.Monster.Existence.TwoPoint.GammaExclTwoBLeaf
public import CFSG.Monster.Existence.TwoPoint.GammaExclLeaf1
public import CFSG.Monster.Existence.TwoPoint.GammaExclLeaf2
public import CFSG.Monster.Existence.TwoPoint.GammaExclLeaf3
public import CFSG.Monster.Existence.TwoPoint.GammaExclLeaf4
public import CFSG.Monster.Existence.TwoPoint.GammaExclLeaf5
public import CFSG.Monster.Existence.TwoPoint.GammaExclLeaf6
public import CFSG.Monster.Existence.TwoPoint.GammaExclLeaf7
public import CFSG.Monster.Existence.TwoPoint.GammaExclLeaf8
public import CFSG.Monster.Existence.TwoPoint.GammaExclLeaf9
public import CFSG.Monster.Existence.TwoPoint.GammaExclCheck
public import CFSG.Monster.Existence.TwoPoint.GammaExclTwoBCheck

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess

theorem gxNodeCheck_ok_of
    {j : ℕ} (h2 : 2 ≤ j) (h23 : j < 23) : gxNodeNe j := by
  interval_cases j
  · exact gxNodeCheck_ok_2
  · exact gxNodeCheck_ok_3
  · exact gxNodeCheck_ok_4
  · exact gxNodeCheck_ok_5
  · exact gxNodeCheck_ok_6
  · exact gxNodeCheck_ok_7
  · exact gxNodeCheck_ok_8
  · exact gxNodeCheck_ok_9
  · exact gxNodeCheck_ok_10
  · exact gxNodeCheck_ok_11
  · exact gxNodeCheck_ok_12
  · exact gxNodeCheck_ok_13
  · exact gxNodeCheck_ok_14
  · exact gxNodeCheck_ok_15
  · exact gxNodeCheck_ok_16
  · exact gxNodeCheck_ok_17
  · exact gxNodeCheck_ok_18
  · exact gxNodeCheck_ok_19
  · exact gxNodeCheck_ok_20
  · exact gxNodeCheck_ok_21
  · exact gxNodeCheck_ok_22

theorem deltaHat_not_commute_betaPrime
    {j : ℕ} (h2 : 2 ≤ j) (h23 : j < 23) :
    deltaHat j * betaPrime ≠ betaPrime * deltaHat j :=
  (gxNodeCheck_sound (gxNodeCheck_ok_of h2 h23)).2

theorem deltaHat_not_commute_alpha
    {j : ℕ} (h1 : 1 ≤ j) (h23 : j < 23) (h9 : j ≠ 9) :
    deltaHat j * fiAlpha ≠ fiAlpha * deltaHat j := by
  rcases Nat.eq_or_lt_of_le h1 with rfl | h2
  · exact deltaHat_one_not_commute_alpha
  · exact (gxNodeCheck_sound (gxNodeCheck_ok_of h2 h23)).1 h9

theorem xHat_nine : xHat 9 = gammaZero * gxT 9 := by
  have e : gxParent 9 = 1 := by decide
  rw [xHat_succ (by omega) (by omega), e, xHat_one]

theorem isConj_xGriess_xHat_nine :
    IsConj xGriess (xHat 9) :=
  gxTwoBCheck_sound gxTwoBCheck_ok

theorem not_isConj_tGriess_xHat_nine :
    ¬ IsConj tGriess (xHat 9) := fun h =>
  not_isConj_xGriess_tGriess (isConj_xGriess_xHat_nine.trans h.symm)

theorem not_isConj_tGriess_gammaZero_mul_gxT_nine :
    ¬ IsConj tGriess (gammaZero * gxT 9) := by
  rw [← xHat_nine]
  exact not_isConj_tGriess_xHat_nine

theorem gxT_mul_self
    (j : ℕ) : gxT j * gxT j = 1 := by
  unfold gxT
  have hγ := gammaZero_mul_self
  calc gxW (gxWord j) * gammaZero * (gxW (gxWord j))⁻¹ *
        (gxW (gxWord j) * gammaZero * (gxW (gxWord j))⁻¹)
      = gxW (gxWord j) * (gammaZero * gammaZero) * (gxW (gxWord j))⁻¹ := by group
    _ = 1 := by rw [hγ]; group

theorem gammaZero_mul_gxT_nine :
    gammaZero * gxT 9 = gxT 9 * gammaZero := by
  obtain ⟨c, hc⟩ := isConj_iff.1 isConj_xGriess_xHat_nine
  have hx : xHat 9 * xHat 9 = 1 := by
    rw [← hc]
    calc c * xGriess * c⁻¹ * (c * xGriess * c⁻¹) = c * (xGriess * xGriess) * c⁻¹ := by group
      _ = 1 := by rw [xGriess_mul_self]; group
  rw [xHat_nine] at hx
  have hT := gxT_mul_self 9
  have hγ := gammaZero_mul_self
  have h1 : gammaZero * gxT 9 = (gammaZero * gxT 9)⁻¹ := eq_inv_of_mul_eq_one_left hx
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hT, inv_eq_of_mul_eq_one_right hγ] at h1
  exact h1

theorem isConj_xHat_nine_fiAlpha_mul_deltaHat :
    IsConj (xHat 9) (fiAlpha * deltaHat 9) :=
  isConj_iff.2 ⟨gammaZero * fiAlpha, fiAlpha_mul_deltaHat_nine.symm⟩

theorem not_isConj_tGriess_fiAlpha_mul_deltaHat_nine :
    ¬ IsConj tGriess (fiAlpha * deltaHat 9) := fun h =>
  not_isConj_tGriess_xHat_nine (h.trans isConj_xHat_nine_fiAlpha_mul_deltaHat.symm)

theorem not_isConj_tGriess_fiBeta_mul_twisted_gamma_nine :
    ¬ IsConj tGriess (fiBeta * (fiAlpha * (fiBeta * deltaHat 9 * fiBeta) * fiAlpha)) := fun h =>
  not_isConj_tGriess_fiAlpha_mul_deltaHat_nine
    (h.trans (isConj_iff.2 ⟨fiAlpha * fiBeta, fiBeta_mul_twisted_gamma_nine.symm⟩).symm)

end CFSG.Monster.Existence
