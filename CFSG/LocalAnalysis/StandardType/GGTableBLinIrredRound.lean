module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinIrredMain
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMore

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTableBActionInputOn_of_not_linDvd {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGLinDvdLabel p lab) :
    GGTableBActionInputOn S :=
  (ggTableBActionInputOn_linDvd_holds.or h).mono fun p lab hlab => by
    by_cases hl : GGLinDvdLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

end CFSG.StandardType

end
