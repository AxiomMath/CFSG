module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.FourForms
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.QForms
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.ResidualQ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTwD4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Holds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.G2GenMain
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenGeoMain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open TenFive.Three


theorem w4Lem10_5Four_of_G2_omega (hG2 : InvolGenG2) (hOm : OmegaSevenCover) : W4Lem10_5Four :=
  w4Lem10_5Four_of_residualThree
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    (w4Lem10_5Q_of_residualQ w4Lem7_4_holds
      (TenFive.w4Lem10_5ResidualQ_of_involQ
        CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
        TenFive.w4Lem10_5InvolQ_holds))
    (w4Lem10_5ResidualThree_of_G2_omega hG2 hOm)

theorem w4Lem10_5Four_holds : W4Lem10_5Four :=
  w4Lem10_5Four_of_G2_omega involGenG2_holds omegaSevenCover_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
