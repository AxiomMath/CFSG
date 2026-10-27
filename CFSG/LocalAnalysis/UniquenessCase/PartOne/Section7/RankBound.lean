module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Config

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem pRank_pPrimeCore_le_three (k : Sec7Core4 G) {H : Subgroup G}
    (hH : Config k H) {q : ℕ} (hq : q.Prime) :
    CFSG.Open.pRank q ((CFSG.pPrimeCore k.p ↥H).map H.subtype) ≤ 3 :=
  k.rankK H hH.not_le hH.two_le_pRank q hq

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
