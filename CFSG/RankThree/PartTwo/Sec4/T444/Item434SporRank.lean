module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporKit
public import CFSG.RankThree.PartTwo.Sec4.Census.TwoCoverCensusResidual
public import CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverF2
public import CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverF5

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Item434Spor Census.SporadicTwoCover

section Families


theorem item434SporAtCard_suz_nine :
    Item434SporAtCard .Suz 9 :=
  item434SporAtCard_nine_of
    (exists_e27_of_two_lt_pRank (by have := Census.three_lt_pRank_suz; omega))
    (item434SporAtNineCover_of_rankFour Census.tripleCoverSuzRankFour)

theorem item434SporAtCard_co3_nine :
    Item434SporAtCard .Co3 9 :=
  item434SporAtCard_nine_of
    (exists_e27_of_two_lt_pRank (by have := three_lt_pRank_co3; omega))
    (item434SporAtNineCover_of_rankFour Census.tripleCoverSporadicRankFour_Co3)

theorem item434SporAtCard_co2_nine :
    Item434SporAtCard .Co2 9 :=
  item434SporAtCard_nine_of
    (exists_e27_of_two_lt_pRank (by have := three_lt_pRank_co2; omega))
    (item434SporAtNineCover_of_rankFour Census.tripleCoverSporadicRankFour_Co2)

theorem item434SporAtCard_hn_nine :
    Item434SporAtCard .HN 9 :=
  item434SporAtCard_nine_of
    (exists_e27_of_two_lt_pRank (by have := three_lt_pRank_hn; omega))
    (item434SporAtNineCover_of_rankFour Census.tripleCoverSporadicRankFour_HN)

theorem item434SporAtCard_ly_nine :
    Item434SporAtCard .Ly 9 :=
  item434SporAtCard_nine_of
    (exists_e27_of_two_lt_pRank (by have := three_lt_pRank_ly; omega))
    (item434SporAtNineCover_of_rankFour Census.tripleCoverSporadicRankFour_Ly)

theorem item434SporAtCard_th_nine :
    Item434SporAtCard .Th 9 :=
  item434SporAtCard_nine_of
    (exists_e27_of_two_lt_pRank (by have := three_lt_pRank_th; omega))
    (item434SporAtNineCover_of_rankFour Census.tripleCoverSporadicRankFour_Th)

theorem item434SporAtCard_onan_nine_of
    (hc : Item434SporAtNineCover .ONan) : Item434SporAtCard .ONan 9 :=
  item434SporAtCard_nine_of
    (exists_e27_of_two_lt_pRank (by have := three_lt_pRank_onan; omega)) hc

theorem item434SporAtCard_mcl_nine_of
    (hc : Item434SporAtNineCover .McL) :
    Item434SporAtCard .McL 9 :=
  item434SporAtCard_nine_of
    (exists_e27_of_two_lt_pRank (by have := three_lt_pRank_mcl; omega)) hc

end Families

end CFSG.RankThree.PartTwo.Sec4
