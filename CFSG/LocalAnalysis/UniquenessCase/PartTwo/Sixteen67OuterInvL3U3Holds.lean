module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGCite
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67OuterL3Odd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67OuterL3Even
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67OuterU3Odd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

theorem k67OuterInvL3U3_holds : K67OuterInvL3U3 := by
  intro J _ _ p f hS α hα hαout y hy
  rcases hS with ⟨hq, hL⟩ | ⟨hp2, hq, hU⟩
  · by_cases hp2 : p = 2
    · subst hp2
      exact orderOf_le_of_outer_involution_psl_even hq hL hα hαout hy
    · exact orderOf_le_of_outer_involution_psl_odd hp2 hq hL hα hαout hy
  · exact orderOf_le_of_outer_involution_psu_odd hp2 hq hU hα hαout hy

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
