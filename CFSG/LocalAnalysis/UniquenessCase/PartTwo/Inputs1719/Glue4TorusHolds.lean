module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Glue4TorusReduction
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Glue4TorusL2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Glue4TorusSz
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Glue4TorusU3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Glue4TorusSp4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem k_19_glue4_torus_holds : K_19_glue4_torus :=
  k_19_glue4_torus_of_families
    (fun _ _ _ _ _ hX => cartanAt_of_isSp4 hX)
    (fun _ _ _ _ _ hY => cartanAt_of_isL2 hY)
    (fun _ _ _ _ _ hY => cartanAt_of_isSz hY)
    (fun _ _ _ _ hn hY => cartanAt_of_isU3 (by omega) hY)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
