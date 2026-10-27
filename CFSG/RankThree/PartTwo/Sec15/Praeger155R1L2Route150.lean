module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2Route150
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent340
public import CFSG.RankThree.S4Free.StellmacherSzAllProved
public import CFSG.RankThree.PartTwo.Sec14.Item1411_3RHolds
public import CFSG.RankThree.PartTwo.Sec15.MathAsch155R1PtInputs
public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1Lemma95

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec15.Sylow155R1
  CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.LocalRank CFSG.PGLModel

theorem item153Main_at_a7_m22
    (h316 : Sec19.Item316) (h148 : Item148R)
    (h149 : Sec16.Item149S14) (h134 : Item134) (h135 : Item135) (h137 : Item137)
    (h142 : Item142AllS14) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h142c : Concl142S14) (h143 : Concl143S14) (h146 : Item146S14) (h1444 : Item1444S14)
    (hbot : Item145BotS14) (h148HJ : Item148HJS14) (hSz : KFacts.KPSz)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L)
    (hL : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    Item153Main A (lB A) := by
  have hHJ : ¬ AllPointsHJ A :=
    Proof15Res6.not_allPointsHJ_of_isEmpty hR.toSec14Std
      (Proof15Res6.isEmpty_j2_of_types (Or.inr hL))
  have h152 : Item152 A (lB A) :=
    Res1PtInputs.item152_at h134 h48 hR hHJ
      (step152CompR_of_item148R h149 h148 h134 h48 h415 hSz G A c L hR)
  exact Res1PtInputs.item153Main_at h316 h149 h148 h134 h135 h137 h142 h48 h415 h142c h143 h146
    h1444 hbot h148HJ hR h152

theorem res1ZExclLeN_l2_a7_of_h340_h150
    (h316 : Sec19.Item316) (hst : StellmacherKP)
    (h340 : Res1Thm340 (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) Res1OpenL2Type)
    (h150 : Res1Thm150b (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) Res1OpenL2Type) :
    Res1ZExclLeN (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) Res1OpenL2Type :=
  Liebeck155R1L2.res1ZExclLeN_l2_a7_of_route150 Sec14.Ronan148M.concl142S14_holds hst
    Sec14.Ronan149.item145BotS14_holds Sec14.Ronan149.item1444S14_holds
    Sec14.Ronan149.item149S14_holds Sec14.Ronan148M.item148R_holds
    (fun G _ _ A c L hR hq =>
      item153Main_at_a7_m22 h316 Sec14.Ronan148M.item148R_holds Sec14.Ronan149.item149S14_holds
        CFSG.RankThree.PartTwo.item134_holds CFSG.RankThree.PartTwo.item135_holds
        Sec13.Ronan137H.item137_holds CFSG.RankThree.PartTwo.item142AllS14_holds
        Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15
        Sec14.Ronan148M.concl142S14_holds Sec14.Ronan148M.concl143S14_holds
        Proof148FourK.item146S14_holds Sec14.Ronan149.item1444S14_holds
        Sec14.Ronan149.item145BotS14_holds (item148HJS14_of_wired Sec14.Ronan148M.item148S14_holds)
        KFacts.kpSz hR (Or.inl hq))
    (fun G _ _ A c L X K Y M T P' Yc z hτ =>
      Res1PtInputs.claim153Normal_at Sec14.Ronan148M.item148R_holds
        Sec14.Ronan149.item149S14_holds CFSG.RankThree.PartTwo.item134_holds
        Close.closed_sec4Item4_8 CFSG.RankThree.PartTwo.item142AllS14_holds
        (item1411_1R_of claim1411LocalR_holds) hτ.sec15 hτ.omega
        (Res1PtInputs.item152_at CFSG.RankThree.PartTwo.item134_holds Close.closed_sec4Item4_8
          hτ.sec15
          (Proof15Res6.not_allPointsHJ_of_isEmpty hτ.std
            (Proof15Res6.isEmpty_j2_of_types (Or.inr (Or.inl hτ.q))))
          (step152CompR_of_item148R Sec14.Ronan149.item149S14_holds
            Sec14.Ronan148M.item148R_holds CFSG.RankThree.PartTwo.item134_holds
            Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15 KFacts.kpSz G A c L hτ.sec15))
        (item153Main_at_a7_m22 h316 Sec14.Ronan148M.item148R_holds
          Sec14.Ronan149.item149S14_holds CFSG.RankThree.PartTwo.item134_holds
          CFSG.RankThree.PartTwo.item135_holds Sec13.Ronan137H.item137_holds
          CFSG.RankThree.PartTwo.item142AllS14_holds Close.closed_sec4Item4_8
          Sec4.Sporadic.rank3II_4_15 Sec14.Ronan148M.concl142S14_holds
          Sec14.Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds
          Sec14.Ronan149.item1444S14_holds Sec14.Ronan149.item145BotS14_holds
          (item148HJS14_of_wired Sec14.Ronan148M.item148S14_holds) KFacts.kpSz hτ.sec15
          (Or.inl hτ.q)))
    h340 h150

theorem res1ZExclLeN_l2_m22_of_h340_h150
    (h316 : Sec19.Item316) (hst : StellmacherKP)
    (h340 : Res1Thm340 (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) Res1OpenL2Type)
    (h150 : Res1Thm150b (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) Res1OpenL2Type) :
    Res1ZExclLeN (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) Res1OpenL2Type :=
  Liebeck155R1L2.res1ZExclLeN_l2_m22_of_route150 Sec14.Ronan148M.concl142S14_holds hst
    Sec14.Ronan149.item145BotS14_holds Sec14.Ronan149.item1444S14_holds
    Sec14.Ronan149.item149S14_holds Sec14.Ronan148M.item148R_holds
    (fun G _ _ A c L hR hq =>
      item153Main_at_a7_m22 h316 Sec14.Ronan148M.item148R_holds Sec14.Ronan149.item149S14_holds
        CFSG.RankThree.PartTwo.item134_holds CFSG.RankThree.PartTwo.item135_holds
        Sec13.Ronan137H.item137_holds CFSG.RankThree.PartTwo.item142AllS14_holds
        Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15
        Sec14.Ronan148M.concl142S14_holds Sec14.Ronan148M.concl143S14_holds
        Proof148FourK.item146S14_holds Sec14.Ronan149.item1444S14_holds
        Sec14.Ronan149.item145BotS14_holds (item148HJS14_of_wired Sec14.Ronan148M.item148S14_holds)
        KFacts.kpSz hR (Or.inr hq))
    (fun G _ _ A c L X K Y M T P' Yc z hτ =>
      Res1PtInputs.claim153Normal_at Sec14.Ronan148M.item148R_holds
        Sec14.Ronan149.item149S14_holds CFSG.RankThree.PartTwo.item134_holds
        Close.closed_sec4Item4_8 CFSG.RankThree.PartTwo.item142AllS14_holds
        (item1411_1R_of claim1411LocalR_holds) hτ.sec15 hτ.omega
        (Res1PtInputs.item152_at CFSG.RankThree.PartTwo.item134_holds Close.closed_sec4Item4_8
          hτ.sec15
          (Proof15Res6.not_allPointsHJ_of_isEmpty hτ.std
            (Proof15Res6.isEmpty_j2_of_types (Or.inr (Or.inr hτ.q))))
          (step152CompR_of_item148R Sec14.Ronan149.item149S14_holds
            Sec14.Ronan148M.item148R_holds CFSG.RankThree.PartTwo.item134_holds
            Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15 KFacts.kpSz G A c L hτ.sec15))
        (item153Main_at_a7_m22 h316 Sec14.Ronan148M.item148R_holds
          Sec14.Ronan149.item149S14_holds CFSG.RankThree.PartTwo.item134_holds
          CFSG.RankThree.PartTwo.item135_holds Sec13.Ronan137H.item137_holds
          CFSG.RankThree.PartTwo.item142AllS14_holds Close.closed_sec4Item4_8
          Sec4.Sporadic.rank3II_4_15 Sec14.Ronan148M.concl142S14_holds
          Sec14.Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds
          Sec14.Ronan149.item1444S14_holds Sec14.Ronan149.item145BotS14_holds
          (item148HJS14_of_wired Sec14.Ronan148M.item148S14_holds) KFacts.kpSz hτ.sec15
          (Or.inr hτ.q)))
    h340 h150

theorem claim153Normal_tau_a7
    (h316 : Sec19.Item316) {P : ∀ (Y : Type) [Group Y], Prop} :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Res1Tau (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) P A c L X K Y M T P' Yc z →
        Claim153Normal A (lB A) := by
  intro G _ _ A c L X K Y M T P' Yc z hτ
  exact Res1PtInputs.claim153Normal_at Sec14.Ronan148M.item148R_holds
    Sec14.Ronan149.item149S14_holds CFSG.RankThree.PartTwo.item134_holds
    Close.closed_sec4Item4_8 CFSG.RankThree.PartTwo.item142AllS14_holds
    (item1411_1R_of claim1411LocalR_holds) hτ.sec15 hτ.omega
    (Res1PtInputs.item152_at CFSG.RankThree.PartTwo.item134_holds Close.closed_sec4Item4_8
      hτ.sec15
      (Proof15Res6.not_allPointsHJ_of_isEmpty hτ.std
        (Proof15Res6.isEmpty_j2_of_types (Or.inr (Or.inl hτ.q))))
      (step152CompR_of_item148R Sec14.Ronan149.item149S14_holds
        Sec14.Ronan148M.item148R_holds CFSG.RankThree.PartTwo.item134_holds
        Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15 KFacts.kpSz G A c L hτ.sec15))
    (item153Main_at_a7_m22 h316 Sec14.Ronan148M.item148R_holds Sec14.Ronan149.item149S14_holds
      CFSG.RankThree.PartTwo.item134_holds CFSG.RankThree.PartTwo.item135_holds
      Sec13.Ronan137H.item137_holds CFSG.RankThree.PartTwo.item142AllS14_holds
      Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15 Sec14.Ronan148M.concl142S14_holds
      Sec14.Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds
      Sec14.Ronan149.item1444S14_holds Sec14.Ronan149.item145BotS14_holds
      (item148HJS14_of_wired Sec14.Ronan148M.item148S14_holds) KFacts.kpSz hτ.sec15
      (Or.inl hτ.q))

theorem claim153Normal_tau_m22
    (h316 : Sec19.Item316) {P : ∀ (Y : Type) [Group Y], Prop} :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Res1Tau (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) P A c L X K Y M T
        P' Yc z → Claim153Normal A (lB A) := by
  intro G _ _ A c L X K Y M T P' Yc z hτ
  exact Res1PtInputs.claim153Normal_at Sec14.Ronan148M.item148R_holds
    Sec14.Ronan149.item149S14_holds CFSG.RankThree.PartTwo.item134_holds
    Close.closed_sec4Item4_8 CFSG.RankThree.PartTwo.item142AllS14_holds
    (item1411_1R_of claim1411LocalR_holds) hτ.sec15 hτ.omega
    (Res1PtInputs.item152_at CFSG.RankThree.PartTwo.item134_holds Close.closed_sec4Item4_8
      hτ.sec15
      (Proof15Res6.not_allPointsHJ_of_isEmpty hτ.std
        (Proof15Res6.isEmpty_j2_of_types (Or.inr (Or.inr hτ.q))))
      (step152CompR_of_item148R Sec14.Ronan149.item149S14_holds
        Sec14.Ronan148M.item148R_holds CFSG.RankThree.PartTwo.item134_holds
        Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15 KFacts.kpSz G A c L hτ.sec15))
    (item153Main_at_a7_m22 h316 Sec14.Ronan148M.item148R_holds Sec14.Ronan149.item149S14_holds
      CFSG.RankThree.PartTwo.item134_holds CFSG.RankThree.PartTwo.item135_holds
      Sec13.Ronan137H.item137_holds CFSG.RankThree.PartTwo.item142AllS14_holds
      Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15 Sec14.Ronan148M.concl142S14_holds
      Sec14.Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds
      Sec14.Ronan149.item1444S14_holds Sec14.Ronan149.item145BotS14_holds
      (item148HJS14_of_wired Sec14.Ronan148M.item148S14_holds) KFacts.kpSz hτ.sec15
      (Or.inr hτ.q))

theorem res1ZExclLeN_l2_a7_of_h150
    (h316 : Sec19.Item316) (hst : StellmacherKP)
    (h150 : Res1Thm150b (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) Res1OpenL2Type) :
    Res1ZExclLeN (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) Res1OpenL2Type :=
  res1ZExclLeN_l2_a7_of_h340_h150 h316 hst
    (res1Thm340_a7 Sec14.Ronan149.item145BotS14_holds Sec14.Ronan149.item1444S14_holds
      Sec14.Ronan148M.item148R_holds Sec14.Ronan149.item149S14_holds KFacts.kpSz
      (claim153Normal_tau_a7 h316))
    h150

theorem res1ZExclLeN_l2_m22_of_h150
    (h316 : Sec19.Item316) (hst : StellmacherKP)
    (h150 : Res1Thm150b (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
      Res1OpenL2Type) :
    Res1ZExclLeN (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
      Res1OpenL2Type :=
  res1ZExclLeN_l2_m22_of_h340_h150 h316 hst
    (res1Thm340_m22 Sec14.Ronan149.item145BotS14_holds Sec14.Ronan149.item1444S14_holds
      Sec14.Ronan148M.item148R_holds Sec14.Ronan149.item149S14_holds KFacts.kpSz
      (claim153Normal_tau_m22 h316))
    h150

theorem stellmacherKP_holds
    : StellmacherKP :=
  ⟨CFSG.RankThree.S4Free.Stell34.stellmacherSzAll_proved, KFacts.kpSz⟩

theorem res1ZExclLeN_l2_a7
    (h316 : Sec19.Item316)
    (h150 : Res1Thm150b (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) Res1OpenL2Type) :
    Res1ZExclLeN (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) Res1OpenL2Type :=
  res1ZExclLeN_l2_a7_of_h150 h316 stellmacherKP_holds h150

theorem res1ZExclLeN_l2_m22
    (h316 : Sec19.Item316)
    (h150 : Res1Thm150b (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
      Res1OpenL2Type) :
    Res1ZExclLeN (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
      Res1OpenL2Type :=
  res1ZExclLeN_l2_m22_of_h150 h316 stellmacherKP_holds h150

theorem item153Main_at_l3_a7_m22
    (h316 : Sec19.Item316) (h148 : Item148R)
    (h149 : Sec16.Item149S14) (h134 : Item134) (h135 : Item135) (h137 : Item137)
    (h142 : Item142AllS14) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h142c : Concl142S14) (h143 : Concl143S14) (h146 : Item146S14) (h1444 : Item1444S14)
    (hbot : Item145BotS14) (h148HJ : Item148HJS14) (hSz : KFacts.KPSz)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L)
    (hL : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    Item153Main A (lB A) := by
  have hHJ : ¬ AllPointsHJ A :=
    Proof15Res6.not_allPointsHJ_of_isEmpty hR.toSec14Std
      (Proof15Res6.isEmpty_j2_of_types hL)
  have h152 : Item152 A (lB A) :=
    Res1PtInputs.item152_at h134 h48 hR hHJ
      (step152CompR_of_item148R h149 h148 h134 h48 h415 hSz G A c L hR)
  exact Res1PtInputs.item153Main_at h316 h149 h148 h134 h135 h137 h142 h48 h415 h142c h143 h146
    h1444 hbot h148HJ hR h152

theorem pCoreOf_two_le_normalizer_of_mem_scriptY0Star_at
    (h316 : Sec19.Item316)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L K : Subgroup G}
    (hR : Sec15R G A c L)
    (hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hK : K ∈ scriptY0Star A (lB A))
    (hWH : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (h3L : 3 ∣ Nat.card L) :
    CFSG.Open.pCoreOf 2 L ≤ Subgroup.normalizer (K : Set G) := by
  have hS := hR.toSec14Std
  have hHJ : ¬ AllPointsHJ A :=
    Proof15Res6.not_allPointsHJ_of_isEmpty hS
      (Proof15Res6.isEmpty_j2_of_types (Or.inl hL3))
  have h152 : Item152 A (lB A) :=
    Res1PtInputs.item152_at CFSG.RankThree.PartTwo.item134_holds Close.closed_sec4Item4_8 hR hHJ
      (step152CompR_of_item148R Sec14.Ronan149.item149S14_holds Sec14.Ronan148M.item148R_holds
        CFSG.RankThree.PartTwo.item134_holds Close.closed_sec4Item4_8
        Sec4.Sporadic.rank3II_4_15 KFacts.kpSz G A c L hR)
  exact Sylow155R1.pCoreOf_two_le_normalizer_of_mem_scriptY0Star hR hK hWH
    (item153Main_at_l3_a7_m22 h316 Sec14.Ronan148M.item148R_holds Sec14.Ronan149.item149S14_holds
      CFSG.RankThree.PartTwo.item134_holds CFSG.RankThree.PartTwo.item135_holds
      Sec13.Ronan137H.item137_holds CFSG.RankThree.PartTwo.item142AllS14_holds
      Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15 Sec14.Ronan148M.concl142S14_holds
      Sec14.Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds
      Sec14.Ronan149.item1444S14_holds Sec14.Ronan149.item145BotS14_holds
      (item148HJS14_of_wired Sec14.Ronan148M.item148S14_holds) KFacts.kpSz hR (Or.inl hL3))
    (Res1PtInputs.claim153Obs_at Sec14.Ronan148M.item148R_holds Sec14.Ronan149.item149S14_holds hR
      h152)
    (item1411_1R_of claim1411LocalR_holds G A c L hR)
    (Sec14.Ronan148M.concl142S14_holds G A c L hS)
    CFSG.RankThree.PartTwo.item135_holds h3L

end CFSG.RankThree.PartTwo.Sec15
