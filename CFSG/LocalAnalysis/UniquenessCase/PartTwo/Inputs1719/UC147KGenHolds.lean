module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC147KGen
public import CFSG.LocalAnalysis.UniquenessCase.UC1K32
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen147.J1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen147.L2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen147.L3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen147.U3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open

theorem kGen147_of_k32 (hK32 : UCK.K32) : KGen147 := by
  intro K _ _ hKg hG hna h3 B R hB hR hR49 hBR hRB H hBH hYH
  have hpair : KGen.IsKGenPair B R := ⟨hB, hR, hR49, hBR, hRB⟩
  rcases hK32 K hKg hG hna h3 with ⟨p, f, hL⟩ | ⟨p, f, hq, hL⟩ | ⟨p, f, hq, hL⟩ | hJ
  · exact KGen.kGenSpans_of_lieModel_psl2 hL hG hna h3 hpair H hBH hYH
  · exact KGen.kGenSpans_of_lieModel_psl3 hq hL hpair H hBH hYH
  · exact KGen.kGenSpans_of_lieModel_psu3 hq hL hG hna h3 hpair H hBH hYH
  · exact KGen.kGenSpans_of_isSpor_J1 hJ hpair H hBH hYH

section Holds


theorem kGen147_holds : KGen147 :=
  kGen147_of_k32 UCK.k32_holds

end Holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
