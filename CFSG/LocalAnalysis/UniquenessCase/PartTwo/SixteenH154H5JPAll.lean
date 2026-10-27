module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPOrthC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPSL2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPStC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem k_JonesParshallH1_holds :
    K_JonesParshallH1 := by
  unfold K_JonesParshallH1
  intro X _ _ hX L
  refine ⟨fun hrow => ?_, fun h => ?_⟩
  · rcases hrow with hA | hO2 | hO3 | ⟨hSt, hirr⟩
    · exact s16jp_row_A5 hX hA
    · exact s16jp_row_O4 hX (m := 2) (by norm_num) hO2
    · exact s16jp_row_O4 hX (m := 3) (by norm_num) hO3
    · exact s16jp_row_St8 hX hSt hirr
  · exact s16jp_row_SL2 hX h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
