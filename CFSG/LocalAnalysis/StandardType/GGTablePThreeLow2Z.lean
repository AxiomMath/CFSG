module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6Narrow
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableZ

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

@[expose] def TwE6A2CentreInputTwo : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twE6 → lab.n = 1 →
    LargeEvenLabelAll lab (TwE6A2CentreCont lab.n)

end CFSG.StandardType.TablePThreeKG

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTablePThreeKnownRestSixLow2Z : Prop :=
  TablePThreeKG.KnownSixOn (fun i => i ≠ 0 ∧ i ≠ 10 ∧ i ≠ 5 ∧ i ≠ 6 ∧ i ≠ 2 ∧ i ≠ 7) ∧
    TablePThreeKG.KnownOverSix (TablePThreeKG.E6SmallOn 5) ∧
    (TablePThreeKG.TwE6A2CentreInputTwo →
      TablePThreeKG.KnownOverSix (TablePThreeKG.E6SmallOn 6)) ∧
    TablePThreeKG.TwE6A2CentreInput ∧ TablePThreeKG.TwE6A2CentreInputTwo

theorem ggTablePThreeKnownRestSixLow_of_low2Z (h : GGTablePThreeKnownRestSixLow2Z)
    (hSymp : TablePThreeKG.KnownOverSix (TablePThreeKG.DatumOn (TablePThreeKG.fam 2)))
    (hF4 : TablePThreeKG.KnownOverSix (TablePThreeKG.DatumOn (TablePThreeKG.fam 7))) :
    GGTablePThreeKnownRestSixLow := by
  refine ⟨fun i hi => ?_, h.2.1, h.2.2.1 h.2.2.2.2, h.2.2.2.1⟩
  by_cases h2 : i = 2
  · subst h2
    exact hSymp
  · by_cases h7 : i = 7
    · subst h7
      exact hF4
    · exact h.1 i ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2, h2, h7⟩

end CFSG.StandardType

end
