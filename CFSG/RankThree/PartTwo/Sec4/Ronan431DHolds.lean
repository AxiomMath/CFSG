module

public import CFSG.RankThree.PartTwo.Sec4.Ronan431DRows
import CFSG.RankThree.PartTwo.Sec4.Ronan431Comp

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan431


theorem k431OpenD : K431OpenD :=
  k431OpenD_of_bridge CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
    (CFSG.LocalAnalysis.GLTheoremA.kdChevDownQ_three_of_lieComp
      CFSG.LocalAnalysis.GLTheoremA.lieComp_holds)
    (Ronan431D.card_eq_360_of_catalogIs_isA6
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds)
    (fun _ _ _ _ _ _ _ _ hc => compOfType_of_cfgS431 hc)

end CFSG.RankThree.PartTwo.Sec4.Ronan431
