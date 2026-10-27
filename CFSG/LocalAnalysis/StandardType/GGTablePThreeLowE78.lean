module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLow2Z

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTablePThreeKnownRestSixLowE78 : Prop :=
  TablePThreeKG.KnownSixOn
      (fun i => i ≠ 0 ∧ i ≠ 10 ∧ i ≠ 5 ∧ i ≠ 6 ∧ i ≠ 2 ∧ i ≠ 7 ∧ i ≠ 8 ∧ i ≠ 9) ∧
    TablePThreeKG.KnownOverSix (TablePThreeKG.E6SmallOn 5) ∧
    (TablePThreeKG.TwE6A2CentreInputTwo →
      TablePThreeKG.KnownOverSix (TablePThreeKG.E6SmallOn 6)) ∧
    TablePThreeKG.TwE6A2CentreInput ∧ TablePThreeKG.TwE6A2CentreInputTwo

theorem ggTablePThreeKnownRestSixLow2Z_of_e78 (h : GGTablePThreeKnownRestSixLowE78)
    (hE78 : ∀ i : Fin 11, i = 8 ∨ i = 9 →
      TablePThreeKG.KnownOverSix (TablePThreeKG.DatumOn (TablePThreeKG.fam i))) :
    GGTablePThreeKnownRestSixLow2Z := by
  refine ⟨fun i hi => ?_, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  by_cases h8 : i = 8
  · exact hE78 i (Or.inl h8)
  · by_cases h9 : i = 9
    · exact hE78 i (Or.inr h9)
    · exact h.1 i ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2, h8, h9⟩

end CFSG.StandardType

end
