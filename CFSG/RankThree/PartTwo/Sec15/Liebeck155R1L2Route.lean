module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2CTheta
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2Main
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1B203
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent162

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem res1_b155_eq_bot_of_tau (h148 : Item148R) (h149 : Sec16.Item149S14)
    {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
    (hQ : ∀ (X : Type) [Group X], Q X →
      Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Sylow155R1.Res1Tau Q P A c L X K Y M T P' Yc z → b155 A M X = ⊥ :=
  fun G _ _ A c L _ _ _ _ _ _ _ _ τ =>
    res1_b155_eq_bot τ.sec15 (hQ _ τ.q) τ.norm (h148 G A c L τ.sec15) (h149 G A c L τ.std)
      τ.ctx τ.endN τ.omega τ.m_eq

theorem res1L2CThetaZ_of_claim (hst : StellmacherKP) (hbot : Item145BotS14)
    (h1444 : Item1444S14) (h149 : Sec16.Item149S14) (h148 : Item148R)
    {Q : ∀ (X : Type) [Group X], Prop}
    (hQ : ∀ (X : Type) [Group X], Q X →
      Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
    (h153 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) → Item153Main A (lB A))
    (hn : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Sylow155R1.Res1Tau Q Res1OpenL2Type A c L X K Y M T P' Yc z → Claim153Normal A (lB A)) :
    Res1L2CThetaZ Q :=
  res1L2CThetaZ_of_b155 hst hbot h1444 h149 h153 hn (res1_b155_eq_bot_of_tau h148 h149 hQ)

theorem res1ZExclLeN_l2_of_route (h142 : Concl142S14) (hst : StellmacherKP)
    (hbot : Item145BotS14) (h1444 : Item1444S14) (h149 : Sec16.Item149S14) (h148 : Item148R)
    {Q : ∀ (X : Type) [Group X], Prop}
    (hQ : ∀ (X : Type) [Group X], Q X →
      Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
    (h153 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) → Item153Main A (lB A))
    (hn : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Sylow155R1.Res1Tau Q Res1OpenL2Type A c L X K Y M T P' Yc z → Claim153Normal A (lB A))
    (h340 : Sylow155R1.Res1Thm340 Q Res1OpenL2Type)
    (h361 : Sylow155R1.Res1Thm361 Q Res1OpenL2Type) :
    Sylow155R1.Res1ZExclLeN Q Res1OpenL2Type :=
  res1ZExclLeN_l2 h142
    (Sylow155R1.res1CentLeMN_of hbot h1444 h149 h153 res1JCyclic_l2 h340 h361)
    (res1L2CThetaZ_of_claim hst hbot h1444 h149 h148 hQ h153 hn)

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2
