module

public import CFSG.RankThree.PartOne.SLBN.U4Nine
public import CFSG.RankThree.PartOne.SRC.Split

public section

namespace CFSG.RankThree.PartOne.SLBN

open TauCeti CFSG.RankThree.PartOne.SRC


theorem rankFourCover_hardU4Nine :
    ∀ i : CFSGIndex, IsHardU4NineIndex i → RankFourCover 3 i.Group := by
  intro i hi
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨li, hv⟩⟩ | ⟨s⟩
  · exact (hi : False).elim
  · exact (hi : False).elim
  · cases li <;> first | exact (hi : False).elim | skip
    obtain ⟨hr, hq⟩ := hi
    subst hr
    rename_i q
    exact rankFourCover_typeTwistedA_four_nine q hv hq
  · exact (hi : False).elim

end CFSG.RankThree.PartOne.SLBN
