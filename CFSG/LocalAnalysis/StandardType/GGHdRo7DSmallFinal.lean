module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DDefs
public import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7DNormalizer
import CFSG.LocalAnalysis.StandardType.GGHdRo7DReduceU
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallAdapt
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallTarget
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallRules
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallNorm
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallCommon
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallExist
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallTrans
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallClass
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallGen
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallModelsBD
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallModelsE7
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallModelsE8

public section

namespace CFSG.StandardType.HdRo7D

namespace Small

theorem d_reflFix_holds : DReflFixLeaf := fun _ _ _ _ _ _ _ _ _ hD _ hrH hr hU =>
  d_reflFix_of_mem hD hrH hr hU

end Small

open CFSG.StandardType.HdRo7D.Small in
theorem d_linSmall_holds : DLinSmallLeaf :=
  d_linSmall_of_target (dSmTarget_of_leaves d_normalizer_holds d_reflFix_holds
    (dSmRules_of_leaves dSmNorm_holds dSmCommon_holds dSmExist_holds) dSmTrans_holds dSmClass_holds
    dSmModelsBD_holds dSmGen_holds dSmModelsE7_holds dSmModelsE8_holds)

end CFSG.StandardType.HdRo7D
