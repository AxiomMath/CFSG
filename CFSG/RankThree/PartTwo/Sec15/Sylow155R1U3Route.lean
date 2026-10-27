module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent340
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3Main
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3Tau
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3Q4G
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent162

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.PGLModel (projSU)

theorem res1ZExclLeN_su3_of_thm340_gen
    (h142 : Concl142S14)
    (hbot : Item145BotS14) (h1444 : Item1444S14) (h149 : Sec16.Item149S14)
    {Q : ∀ (X : Type) [Group X], Prop} (hQE9 : Res1QE9 Q)
    (h153 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) → Item153Main A (lB A))
    (h340 : Res1Thm340 Q Res1OpenSU3Type) (h150 : Res1Thm150b Q Res1OpenSU3Type) :
    Res1ZExclLeN Q Res1OpenSU3Type :=
  res1ZExclLeN_su3_of_centLeM_gen h142
    (res1CentLeMN_of hbot h1444 h149 h153 res1JCyclic_su3 h340
      (res1Thm361_of h149 hQE9 h150 res1Lem154_su3))

theorem res1ZExclLeN_su3_of_route150
    (h131 : Item131) (h142 : Concl142S14) (h142R : Item142R) (hbot : Item145BotS14)
    (h1444 : Item1444S14) (h148 : Item148R) (h149 : Sec16.Item149S14) (hSz : KFacts.KPSz)
    {Q : ∀ (X : Type) [Group X], Prop}
    (hQ : ∀ (X : Type) [Group X], Q X →
      Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
    (hQE9 : Res1QE9 Q)
    (h153 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) → Item153Main A (lB A))
    (hn : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Res1Tau Q Res1OpenSU3Type A c L X K Y M T P' Yc z → Claim153Normal A (lB A))
    (h150 : Res1Thm150b Q Res1OpenSU3Type) :
    Res1ZExclLeN Q Res1OpenSU3Type :=
  res1ZExclLeN_su3_of_centLeM_five h142
    (res1CentLeMN_of hbot h1444 h149 h153 res1JCyclic_su3
      (res1Thm340_of hbot h1444 h148 h149 hSz hQ hQE9 hn)
      (res1Thm361_of h149 hQE9 h150 res1Lem154_su3))
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ τ _ => τ.five_facts_of_a7_m22 h148 hbot h142R h131 hQ

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
