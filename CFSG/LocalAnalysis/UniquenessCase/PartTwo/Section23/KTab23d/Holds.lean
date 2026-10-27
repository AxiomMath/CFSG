module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineK
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LineL2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LineOmega4Minus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LineOmega4Plus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LineSp4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LineSL3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LineSU4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LineOmega6Minus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LineSL4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LineOmega6Plus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LineSp6
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LineOmega8Minus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

theorem kTab23d_holds : KTab23d := by
  intro W _ _ H n hnat hperf hn S ℓ Pℓ Kstar
  exact ⟨KTabD.kTab23d_L2 H n hnat hperf hn S,
    KTabD.kTab23d_omegaMinusFour H n hnat hperf hn S,
    KTabD.kTab23d_omegaPlusFour H n hnat hperf hn S,
    KTabD.kTab23d_sp4 H n hnat hperf hn S,
    KTabD.kTab23d_sl3 H n hnat hperf hn S,
    KTabD.kTab23d_su4 H n hnat hperf hn S,
    KTabD.kTab23d_omegaMinusSix H n hnat hperf hn S,
    KTabD.kTab23d_sl4 H n hnat hperf hn S,
    KTabD.kTab23d_omegaPlusSix H n hnat hperf hn S,
    KTabD.kTab23d_sp6 H n hnat hperf hn S,
    KTabD.kTab23d_omegaMinusEight H n hnat hperf hn S⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
