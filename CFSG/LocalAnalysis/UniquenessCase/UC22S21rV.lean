module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU
public import CFSG.LocalAnalysis.UniquenessCase.UC22UniqueMax
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s22_9_of_S21_22Use
    (D : Data G) (Ch : Choice2011 G)
    (h2122 : S21_22Use D Ch) (h20_4 : S20_4 D) (hn3 : H1930 D → ∀ c : Ctx22b D Ch, 3 ≤ c.n)
    (hV : S22_V D Ch) : S22_9 D Ch :=
  s22_9_of_ASU D Ch h2122 hn3 (uniqueMaxL0T_of_s20_4 D Ch h20_4) (inE229_of_hn3 D Ch hn3) hV

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
