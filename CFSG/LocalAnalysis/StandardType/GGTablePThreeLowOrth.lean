module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLowUni

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTablePThreeKnownRestSixLowOrth : Prop :=
  TablePThreeKG.KnownOverSix (TablePThreeKG.E6SmallOn 5) ∧
    (TablePThreeKG.TwE6A2CentreInputTwo →
      TablePThreeKG.KnownOverSix (TablePThreeKG.E6SmallOn 6)) ∧
    TablePThreeKG.TwE6A2CentreInput ∧ TablePThreeKG.TwE6A2CentreInputTwo

theorem ggTablePThreeKnownRestSixLowUni_of_orth (h : GGTablePThreeKnownRestSixLowOrth)
    (hD : TablePThreeKG.KnownOverSix (TablePThreeKG.DatumOn (TablePThreeKG.fam 3)))
    (hTwD : TablePThreeKG.KnownOverSix (TablePThreeKG.DatumOn (TablePThreeKG.fam 4))) :
    GGTablePThreeKnownRestSixLowUni := by
  refine ⟨fun i hi => ?_, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨h0, h10, h5, h6, h2, h7, h8, h9, h1⟩ := hi
  have hi34 : i = 3 ∨ i = 4 := by
    revert h0 h10 h5 h6 h2 h7 h8 h9 h1
    fin_cases i <;> decide
  rcases hi34 with rfl | rfl
  · exact hD
  · exact hTwD

end CFSG.StandardType

end
