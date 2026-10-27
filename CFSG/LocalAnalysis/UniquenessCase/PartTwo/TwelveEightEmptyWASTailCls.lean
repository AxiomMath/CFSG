module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEightEmptyWASTail
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Main
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASFinal
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5AboveFive
import CFSG.LocalAnalysis.WeakClosure81.RankThreePrimePowerBounds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC


theorem ascTwelveEightEmptyW_of_inputs_AS_tail_cls
    (hC : ∀ (G : Type) [Group G] [Finite G], Standing G → AGL81TheoremC G)
    (h5_11 : WeakClosure81.Asch5_11AS) (h5_13 : WeakClosure81.Asch5_13AS)
    (hCS : WeakClosure81.CitedShapeFacts) (hGS : WeakClosure81.GapShapeFacts)
    (hTI : WeakClosure81.TimmesfeldTIRootInput)
    (hCore : WeakClosure81.OddTranspositionCoreInputSCCls)
    (hList : WeakClosure81.OddTranspListBundleCls)
    (hLie : WeakClosure81.SpPSULieFacts)
    (hRU : WeakClosure81.SevenK.UnitaryRootCommutatorRank) :
    CFSG.Yardstones.Me2c15c2c995a.AscTwelveEightEmptyW :=
  ascTwelveEightEmptyW_of_inputs_AS_tail_shapes hC h5_11 h5_13 hCS hGS
    (fun _ _ _ _ _ => WeakClosure81.thm93Syl_of_classification hCore hList
      (fun Y _ _ => WeakClosure81.SzExcl.sevenSevenTwoInput_holds Y))
    hTI hCore.toInput hList.toInput hLie hRU

theorem ascTwelveEightEmptyW_of_inputs_AS_tail_cls_of_five
    (hC : ∀ (G : Type) [Group G] [Finite G], Standing G → AGL81TheoremC G)
    (h54 : WeakClosure81.Asch5_4) (h512 : WeakClosure81.Asch5_12)
    (hCS : WeakClosure81.CitedShapeFacts) (hGS : WeakClosure81.GapShapeFacts)
    (hTI : WeakClosure81.TimmesfeldTIRootInput)
    (hCore : WeakClosure81.OddTranspositionCoreInputSCCls)
    (hList : WeakClosure81.OddTranspListBundleCls)
    (hLie : WeakClosure81.SpPSULieFacts)
    (hRU : WeakClosure81.SevenK.UnitaryRootCommutatorRank) :
    CFSG.Yardstones.Me2c15c2c995a.AscTwelveEightEmptyW :=
  ascTwelveEightEmptyW_of_inputs_AS_tail_cls hC
    (WeakClosure81.asch5_11AS_of_remaining_inputs h54)
    (WeakClosure81.asch5_13AS_of_inputs h512 WeakClosure81.asch4_11ASPow_holds)
    hCS hGS hTI hCore hList hLie hRU

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
