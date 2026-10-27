module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLowE78

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTablePThreeKnownRestSixLowUni : Prop :=
  TablePThreeKG.KnownSixOn
      (fun i => i ≠ 0 ∧ i ≠ 10 ∧ i ≠ 5 ∧ i ≠ 6 ∧ i ≠ 2 ∧ i ≠ 7 ∧ i ≠ 8 ∧ i ≠ 9 ∧ i ≠ 1) ∧
    TablePThreeKG.KnownOverSix (TablePThreeKG.E6SmallOn 5) ∧
    (TablePThreeKG.TwE6A2CentreInputTwo →
      TablePThreeKG.KnownOverSix (TablePThreeKG.E6SmallOn 6)) ∧
    TablePThreeKG.TwE6A2CentreInput ∧ TablePThreeKG.TwE6A2CentreInputTwo

theorem ggTablePThreeKnownRestSixLowE78_of_uni (h : GGTablePThreeKnownRestSixLowUni)
    (hUni : TablePThreeKG.KnownOverSix (TablePThreeKG.DatumOn (TablePThreeKG.fam 1))) :
    GGTablePThreeKnownRestSixLowE78 := by
  refine ⟨fun i hi => ?_, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  by_cases h1 : i = 1
  · subst h1
    exact hUni
  · exact h.1 i ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2.1,
      hi.2.2.2.2.2.2.2, h1⟩

end CFSG.StandardType

end
