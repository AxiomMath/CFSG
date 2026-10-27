module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1L3B203
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2Route150
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent162

public section

namespace CFSG.RankThree.PartTwo.Sec15.GagenL3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS


theorem res1ZExclLeN_l2_l3_of_route150 (h142 : Concl142S14) (hst : StellmacherKP)
    (hbot : Item145BotS14) (h1444 : Item1444S14) (h149 : Sec16.Item149S14) (h148 : Item148R)
    {Q : ∀ (X : Type) [Group X], Prop} (hQ : ∀ (X : Type) [Group X], Q X → Res1L3Q X)
    (h153 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) → Item153Main A (lB A))
    (hn : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Sylow155R1.Res1Tau Q Res1OpenL2Type A c L X K Y M T P' Yc z → Claim153Normal A (lB A))
    (h340 : Sylow155R1.Res1Thm340 Q Res1OpenL2Type)
    (h150 : Sylow155R1.Res1Thm150b Q Res1OpenL2Type) :
    Sylow155R1.Res1ZExclLeN Q Res1OpenL2Type :=
  Liebeck155R1L2.res1ZExclLeN_l2 h142
    (Sylow155R1.res1CentLeMN_of hbot h1444 h149 h153 Liebeck155R1L2.res1JCyclic_l2 h340
      (Sylow155R1.res1Thm361_of h149 (res1QE9_of_le hQ) h150 Liebeck155R1L2.res1Lem154_l2))
    (Liebeck155R1L2.res1L2CThetaZ_of_b155 hst hbot h1444 h149 h153 hn
      (res1_b155_eq_bot_l3_of_tau h148 h149 hQ))

end CFSG.RankThree.PartTwo.Sec15.GagenL3
