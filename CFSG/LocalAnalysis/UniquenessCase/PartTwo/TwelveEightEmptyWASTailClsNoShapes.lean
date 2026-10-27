module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEightEmptyWASTailCls
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapFinal
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitaryHolds
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCited
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.Main
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedHolds
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Main
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Holds
public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListTriHolds
import CFSG.LocalAnalysis.WeakClosure81.TrialityCentralHolds
import CFSG.LocalAnalysis.WeakClosure81.TrialityMarkedHolds
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreSimpleHolds
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC






theorem ascTwelveEightEmptyW_of_inputs_AS_tail_cls_noShapes
    (hC : ∀ (G : Type) [Group G] [Finite G], Standing G → AGL81TheoremC G) :
    CFSG.Yardstones.Me2c15c2c995a.AscTwelveEightEmptyW :=
  have hCore : WeakClosure81.OddTranspositionCoreInputSCCls :=
    WeakClosure81.oddTranspositionCoreInputSCCls_of_cases
        (WeakClosure81.oddTranspCoreThreeTranspInput_of_simple
            WeakClosure81.oddTranspCoreSimpleInput_holds)
        WeakClosure81.oddTranspCoreRadicalInput_holds
  have hList : WeakClosure81.OddTranspListBundleCls :=
    ⟨WeakClosure81.oddTranspositionListInputClsTri_holds,
      WeakClosure81.trialityMarkedInput_holds, WeakClosure81.trialityCentralInput_holds⟩
  (ascTwelveEightEmptyW_of_inputs_AS_tail_cls_of_five hC WeakClosure81.asch5_4_holds
      WeakClosure81.asch5_12_holds WeakClosure81.citedShapeFacts_holds
      WeakClosure81.gapShapeFacts_holds WeakClosure81.timmesfeldTIRootInput_holds hCore hList
      WeakClosure81.spPSULieFacts_holds WeakClosure81.unitaryRootCommutatorRank_holds)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
