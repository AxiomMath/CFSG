module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1L3L2
import CFSG.RankThree.S4Free.StellmacherSzAllProved
public import CFSG.RankThree.PartTwo.Sec14.Item1411_3RHolds
public import CFSG.RankThree.PartTwo.Sec15.MathAsch155R1PtInputs

public section

namespace CFSG.RankThree.PartTwo.Sec15.GagenL3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec15.Sylow155R1
  CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.LocalRank


theorem item153Main_of_isEmpty_j2
    (h316 : Sec19.Item316) (h148 : Item148R)
    (h149 : Sec16.Item149S14) (h134 : Item134) (h135 : Item135) (h137 : Item137)
    (h142 : Item142AllS14) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h142c : Concl142S14) (h143 : Concl143S14) (h146 : Item146S14) (h1444 : Item1444S14)
    (hbot : Item145BotS14) (h148HJ : Item148HJS14) (hSz : KFacts.KPSz)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L)
    (hJ : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Item153Main A (lB A) :=
  Res1PtInputs.item153Main_at h316 h149 h148 h134 h135 h137 h142 h48 h415 h142c h143 h146 h1444
    hbot h148HJ hR
    (Res1PtInputs.item152_at h134 h48 hR
      (Proof15Res6.not_allPointsHJ_of_isEmpty hR.toSec14Std hJ)
      (step152CompR_of_item148R h149 h148 h134 h48 h415 hSz G A c L hR))


theorem item153Main_of_l3
    (h316 : Sec19.Item316) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L)
    (hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L)) : Item153Main A (lB A) :=
  item153Main_of_isEmpty_j2 h316 Sec14.Ronan148M.item148R_holds Sec14.Ronan149.item149S14_holds
    CFSG.RankThree.PartTwo.item134_holds CFSG.RankThree.PartTwo.item135_holds
    Sec13.Ronan137H.item137_holds CFSG.RankThree.PartTwo.item142AllS14_holds
    Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15 Sec14.Ronan148M.concl142S14_holds
    Sec14.Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds
    Sec14.Ronan149.item1444S14_holds Sec14.Ronan149.item145BotS14_holds
    (item148HJS14_of_wired Sec14.Ronan148M.item148S14_holds) KFacts.kpSz hR
    (Proof15Res6.isEmpty_j2_of_types (Or.inl hL3))

theorem claim153Normal_of_tau_l3
    (h316 : Sec19.Item316) {Q : ∀ (X : Type) [Group X], Prop}
    {P : ∀ (Y : Type) [Group Y], Prop} (hQ : ∀ (X : Type) [Group X], Q X → Res1L3Q X) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Res1Tau Q P A c L X K Y M T P' Yc z → Claim153Normal A (lB A) :=
  fun G _ _ A c L _ _ _ _ _ _ _ _ hτ =>
    Res1PtInputs.claim153Normal_at Sec14.Ronan148M.item148R_holds
      Sec14.Ronan149.item149S14_holds CFSG.RankThree.PartTwo.item134_holds
      Close.closed_sec4Item4_8 CFSG.RankThree.PartTwo.item142AllS14_holds
      (item1411_1R_of claim1411LocalR_holds) hτ.sec15 hτ.omega
      (Res1PtInputs.item152_at CFSG.RankThree.PartTwo.item134_holds Close.closed_sec4Item4_8
        hτ.sec15
        (Proof15Res6.not_allPointsHJ_of_isEmpty hτ.std
          (Proof15Res6.isEmpty_j2_of_types (Or.inl (hQ _ hτ.q).1)))
        (step152CompR_of_item148R Sec14.Ronan149.item149S14_holds
          Sec14.Ronan148M.item148R_holds CFSG.RankThree.PartTwo.item134_holds
          Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15 KFacts.kpSz G A c L hτ.sec15))
      (item153Main_of_l3 h316 hτ.sec15 (hQ _ hτ.q).1)


theorem res1ZExclLeN_l2_l3_of_h340_h150
    (h316 : Sec19.Item316)
    {Q : ∀ (X : Type) [Group X], Prop} (hQ : ∀ (X : Type) [Group X], Q X → Res1L3Q X)
    (h340 : Res1Thm340 Q Res1OpenL2Type) (h150 : Res1Thm150b Q Res1OpenL2Type) :
    Res1ZExclLeN Q Res1OpenL2Type :=
  res1ZExclLeN_l2_l3_of_route150 Sec14.Ronan148M.concl142S14_holds
    ⟨CFSG.RankThree.S4Free.Stell34.stellmacherSzAll_proved, KFacts.kpSz⟩
    Sec14.Ronan149.item145BotS14_holds Sec14.Ronan149.item1444S14_holds
    Sec14.Ronan149.item149S14_holds Sec14.Ronan148M.item148R_holds hQ
    (fun _ _ _ _ _ _ hR hq => item153Main_of_l3 h316 hR (hQ _ hq).1)
    (claim153Normal_of_tau_l3 h316 hQ) h340 h150

end CFSG.RankThree.PartTwo.Sec15.GagenL3
