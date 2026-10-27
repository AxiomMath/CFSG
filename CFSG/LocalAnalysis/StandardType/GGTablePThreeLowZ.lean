module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLowOrth

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTablePThreeKnownRestSixLowZ : Prop :=
  TablePThreeKG.TwE6A2CentreInput ∧ TablePThreeKG.TwE6A2CentreInputTwo

theorem ggTablePThreeKnownRestSixLowOrth_of_z (h : GGTablePThreeKnownRestSixLowZ)
    (hE6 : TablePThreeKG.KnownOverSix (TablePThreeKG.E6SmallOn 5) ∧
      (TablePThreeKG.TwE6A2CentreInputTwo → TablePThreeKG.KnownOverSix (TablePThreeKG.E6SmallOn 6))) :
    GGTablePThreeKnownRestSixLowOrth :=
  ⟨hE6.1, hE6.2, h.1, h.2⟩

end CFSG.StandardType

end
