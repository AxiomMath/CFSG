module

public import CFSG.OddTranspositions.TheoremTwo.SevenOneB
public import CFSG.OddTranspositions.TheoremTwo.ThirdKindExclusion

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge.Asc72

theorem thirdKBenderStatement_holds :
    ThirdKBenderStatement := by
  intro G _ _ D hS _ hL u w v n htri hn hn1 hord
  exact isBenderGroup_thirdK_quotient theoremOne hS hL htri hn hn1 hord

end CFSG.OddTranspositions
