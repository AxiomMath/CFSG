module

public import CFSG.RankThree.PartTwo.Sec15.ThmCM2Mult
public import CFSG.RankThree.PartTwo.Sec15.ThmCMain

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmC

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

theorem pCoreOf_mem_scriptQ_of_scriptY0_free
    (h148 : Sec14.Item148R) (h142 : Sec14.Concl142S14)
    (h146 : Sec14.Item146S14) (h1444 : Sec14.Item1444S14) (hbot : Sec14.Item145BotS14) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A), CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) :=
  pCoreOf_mem_scriptQ_of_scriptY0 kFactM2_of_certificates h148 h142 h146 h1444 hbot

theorem step171CommQ_of_route_free
    (h148 : Sec14.Item148R) (h142 : Sec14.Concl142S14)
    (h146 : Sec14.Item146S14) (h1444 : Sec14.Item1444S14) (hbot : Sec14.Item145BotS14) :
    Sec17.Step171CommQ :=
  step171CommQ_of_route kFactM2_of_certificates h148 h142 h146 h1444 hbot

end CFSG.RankThree.PartTwo.Sec15.ThmC
