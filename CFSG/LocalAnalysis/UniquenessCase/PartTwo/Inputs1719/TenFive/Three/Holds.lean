module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Residual
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.PSL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.PSU
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.PSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.POmega
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.ExcUntwisted
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.ExcE6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.ExcE7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.TwInvol
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Open

theorem w4Lem10_5ResidualThree_of_G2_omega (hG2 : InvolGenG2) (hOm : OmegaSevenCover) :
    W4Lem10_5ResidualThree :=
  w4Lem10_5ResidualThree_of CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
      involAt_PSL involAt_PSU involAt_PSp involAt_POmegaOdd involAt_POmegaPlus involAt_POmegaMinus
      hG2 involAt_F4 involAt_E6 involAt_E7 involAt_E8 involAt_twistedE6 involAt_trialityD4 hOm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
