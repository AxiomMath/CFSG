module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTorusAbelianOmegaPlus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTorusAbelianOmegaMinus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTorusAbelianE6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTorusAbelianTwistedE6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU2OddCoverHolds
public import CFSG.Adapters.Certificate43Check

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem k_BorelTorusAbelian_holds : K_BorelTorusAbelian := by
  have := CFSG.Adapters.certificate43_holds
  exact k_BorelTorusAbelian_of_griess_of_L34_SU2_orthogonal_E6
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20r_nativeGriess k_L34OddCover_holds
    k_SU2OddCover_holds
    (k_BorelTorusAbelian_POmegaPlus_of_griess
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20r_nativeGriess)
    (k_BorelTorusAbelian_POmegaMinus_of_griess
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20r_nativeGriess)
    k_BorelTorusAbelian_E6 k_BorelTorusAbelian_twistedE6

theorem k_BorelTorusAbelianRankGeFour_holds : K_BorelTorusAbelianRankGeFour :=
  k_BorelTorusAbelian_holds.rankGeFour

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
