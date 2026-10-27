module

public import CFSG.RankThree.GF2n.Tim77.Cor2AlphaDefs
public import CFSG.Timmesfeld.CorollaryBMain
public import CFSG.LargeExtraspecial.S8CBFList

public section

namespace CFSG.RankThree.GF2n.Tim77

theorem corBFine_holds :
    CorBFineStatement := by
  intro X _ _ t h
  rcases CFSG.Timmesfeld.CorB.main h with hi | hii | ⟨hdeg, -⟩ | ⟨-, hO⟩
  · exact Or.inl hi
  · exact Or.inr (Or.inl hii)
  · exact Or.inr (Or.inr (Or.inl hdeg))
  · exact Or.inr (Or.inr (Or.inr ⟨_, hO⟩))

theorem corBListSimple_holds :
    CorBListSimpleStatement :=
  fun _ _ h => CFSG.LargeExtraspecial.S8.isSimpleGroup_of_corBList h

end CFSG.RankThree.GF2n.Tim77
