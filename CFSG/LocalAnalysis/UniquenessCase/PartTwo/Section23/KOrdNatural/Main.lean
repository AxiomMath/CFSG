module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwentyThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.Parts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreNatural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

theorem kOrdNatural_holds : KOrdNatural :=
  ⟨kOrd_pCore_eq_bot, kOrd_nontrivial, kOrd_binaryNaturalSL, kOrd_natOmegaMinus_four⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

end
