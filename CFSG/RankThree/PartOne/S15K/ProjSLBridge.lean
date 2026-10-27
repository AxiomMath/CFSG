module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.RankThreeEven

theorem projSL_eq_range_toPGL (n : ℕ) (K : Type*) [Field K] :
    projSL n K =
      (Matrix.SpecialLinearGroup.toPGL :
        Matrix.SpecialLinearGroup (Fin n) K →* Matrix.ProjGenLinGroup (Fin n) K).range := by
  rw [projSL, projImage, Matrix.SpecialLinearGroup.toPGL, MonoidHom.range_comp,
    Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]

@[expose] noncomputable def projSLEquivProjectiveSL (n : ℕ) (K : Type*) [Field K] :
    projSL n K ≃* projectiveSL n K :=
  ((QuotientGroup.quotientMulEquivOfEq
      (by rw [Matrix.SpecialLinearGroup.toPGL_ker, scalars_eq_center] :
        scalars n K = (Matrix.SpecialLinearGroup.toPGL :
          Matrix.SpecialLinearGroup (Fin n) K →* Matrix.ProjGenLinGroup (Fin n) K).ker)).trans
    ((QuotientGroup.quotientKerEquivRange _).trans
      (MulEquiv.subgroupCongr (projSL_eq_range_toPGL n K).symm))).symm

end CFSG.RankThree.PartOne.S15K
