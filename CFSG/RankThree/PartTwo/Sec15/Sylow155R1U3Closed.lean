module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3Route
public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1L2Route150
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150Holds

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.LocalRank


theorem res1ZExclLeN_su3_a7_of_316
    (h316 : Sec19.Item316) :
    Res1ZExclLeN (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) Res1OpenSU3Type := by
  have h153 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L →
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
        Item153Main A (lB A) :=
    fun _ _ _ _ _ _ hR hq =>
      item153Main_at_a7_m22 h316 Sec14.Ronan148M.item148R_holds
        Sec14.Ronan149.item149S14_holds CFSG.RankThree.PartTwo.item134_holds
        CFSG.RankThree.PartTwo.item135_holds Sec13.Ronan137H.item137_holds
        CFSG.RankThree.PartTwo.item142AllS14_holds Close.closed_sec4Item4_8
        Sec4.Sporadic.rank3II_4_15 Sec14.Ronan148M.concl142S14_holds
        Sec14.Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds
        Sec14.Ronan149.item1444S14_holds Sec14.Ronan149.item145BotS14_holds
        (item148HJS14_of_wired Sec14.Ronan148M.item148S14_holds) KFacts.kpSz hR (Or.inl hq)
  have hn : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
      (L X K Y M T P' : Subgroup G) (Yc : Subgroup (Res1Q A L)) (z : G),
      Res1Tau (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) Res1OpenSU3Type A c L
        X K Y M T P' Yc z → Claim153Normal A (lB A) :=
    fun G _ _ A c L X K Y M T P' Yc z hτ =>
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
        (h153 G A c L hτ.sec15 hτ.q)
  exact res1ZExclLeN_su3_of_route150 rank3II_13_1_holds
    Sec14.Ronan148M.concl142S14_holds
    (item142R_of_wired CFSG.RankThree.PartTwo.item142AllS14_holds)
    Sec14.Ronan149.item145BotS14_holds Sec14.Ronan149.item1444S14_holds
    Sec14.Ronan148M.item148R_holds Sec14.Ronan149.item149S14_holds KFacts.kpSz
    (fun _ _ h => Or.inl h) res1QE9_a7 h153 hn Liebeck155R1T150.res1Thm150b_a7

theorem res1ZExclLeN_su3_m22_of_316
    (h316 : Sec19.Item316) :
    Res1ZExclLeN (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
      Res1OpenSU3Type := by
  have h153 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L →
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) →
        Item153Main A (lB A) :=
    fun _ _ _ _ _ _ hR hq =>
      item153Main_at_a7_m22 h316 Sec14.Ronan148M.item148R_holds
        Sec14.Ronan149.item149S14_holds CFSG.RankThree.PartTwo.item134_holds
        CFSG.RankThree.PartTwo.item135_holds Sec13.Ronan137H.item137_holds
        CFSG.RankThree.PartTwo.item142AllS14_holds Close.closed_sec4Item4_8
        Sec4.Sporadic.rank3II_4_15 Sec14.Ronan148M.concl142S14_holds
        Sec14.Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds
        Sec14.Ronan149.item1444S14_holds Sec14.Ronan149.item145BotS14_holds
        (item148HJS14_of_wired Sec14.Ronan148M.item148S14_holds) KFacts.kpSz hR (Or.inr hq)
  have hn : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
      (L X K Y M T P' : Subgroup G) (Yc : Subgroup (Res1Q A L)) (z : G),
      Res1Tau (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) Res1OpenSU3Type A c L
        X K Y M T P' Yc z → Claim153Normal A (lB A) :=
    fun G _ _ A c L X K Y M T P' Yc z hτ =>
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
        (h153 G A c L hτ.sec15 hτ.q)
  exact res1ZExclLeN_su3_of_route150 rank3II_13_1_holds
    Sec14.Ronan148M.concl142S14_holds
    (item142R_of_wired CFSG.RankThree.PartTwo.item142AllS14_holds)
    Sec14.Ronan149.item145BotS14_holds Sec14.Ronan149.item1444S14_holds
    Sec14.Ronan148M.item148R_holds Sec14.Ronan149.item149S14_holds KFacts.kpSz
    (fun _ _ h => Or.inr h) res1QE9_m22 h153 hn Liebeck155R1T150.res1Thm150b_m22

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
