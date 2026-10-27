module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.L2Over17
public import CFSG.LocalAnalysis.ComponentClassification.OddLieL2OrderBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17


theorem k_LieModelNotL2_holds : S17.K_LieModelNotL2 := by
  intro X _ t n r f q' hr hnot hadm hm hl2
  obtain ⟨r', f', -, hr'2, -, -, hm'⟩ := hl2
  have huniq :=
    CFSG.ComponentClassification.CatLeafProof.lieModel_odd_psl_two_unique hm hm' hr hr'2
  rcases hnot with h | h
  · exact h huniq.1
  · exact h huniq.2.1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
