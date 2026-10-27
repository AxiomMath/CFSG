module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineK
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.HoldsB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SU4Line
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Om6mLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.O6pLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.O8mLine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

theorem kAdj_holds : KAdj :=
  KAdjE.kAdj_of_lines (fun _ _ _ H _ h hn => KAdjE.kAdjAt_su4 H h hn)
    (fun _ _ _ H _ h _ => KAdjE.kAdjAt_om6m H h) KAdjE.kAdjAt_omegaPlusSix
    KAdjE.kAdjAt_omegaMinusEight

end CFSG.LocalAnalysis.UniquenessCase.UC22
