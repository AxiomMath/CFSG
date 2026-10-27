module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155BigHost
public import CFSG.RankThree.PartTwo.Sec15.Gagen155BigHostRes1
public import CFSG.RankThree.PartTwo.Sec15.Gagen155Big155w
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJBigClosed
public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1Res1L112From155w
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Fact
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Bal
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Main
import CFSG.RankThree.PartTwo.Sec15.MathAsch1511Of316
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3WRHolds
import CFSG.RankThree.PartTwo.Sec15.Gagen155Y143
import CFSG.RankThree.PartTwo.Sec15.Sylow155L143Holds
import CFSG.RankThree.PartTwo.Sec15.Sylow155KSL3
import CFSG.LocalAnalysis.UniquenessCase.UC1K45SzAut
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1RoutePt

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem step155HostE0WRes1RPtBig_of_res1OpenF
    {Pt : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → Prop}
    (hF : Step155HostE0WRes1TypeFPtBig Pt Res1OpenType) : Step155HostE0WRes1RPtBig Pt :=
  have h143 : Y1SecondFormExcl :=
    y1SecondFormExcl_of_k143Excl Sec11.Close.closed_sec4Item4_1LargePrime
      Sec11.Close.closed_sec4Item4_1ThreeCover Sec11.Close.closed_sec4Item4_3
      Sylow155R1.coverInputs46_closed
      (Sylow155L143.k143Excl_of_inputs Sec11.Close.closed_sec4Item4_1ThreeCover
        Sec11.Close.closed_sec4Item4_3 Sylow155R1.coverInputs46_closed)
  step155HostE0WRes1RPtBig_of_types
    (Sylow155R1.res1TypeFact_of Sec11.Close.closed_sec4Item4_1LargePrime)
    Sylow155R1.step155HostE0WRes1Type_oddL2 Sylow155R1.step155HostE0WRes1Type_oddL3
    Sylow155R1.step155HostE0WRes1Type_j1 Sylow155R1.step155HostE0WRes1Type_small
    Sylow155R1.step155HostE0WRes1Type_l2Odd
    (Sylow155R1.step155HostE0WRes1Type_mid Sec11.Close.closed_sec4Item4_1LargePrime
      Sec11.Close.closed_sec4Item4_1ThreeCover Sec11.Close.closed_sec4Item4_3
      Sylow155R1.coverInputs46_closed h143 Ronan148M.concl142S14_holds
      Ronan149.item1444S14_holds)
    (step155HostE0WRes1TypePtBig_open_of_field Sec11.Close.closed_sec4Item4_1LargePrime
      Sec11.Close.closed_sec4Item4_1ThreeCover Sec11.Close.closed_sec4Item4_3
      Sylow155R1.coverInputs46_closed h143 Ronan148M.concl142S14_holds Ronan149.item1444S14_holds
      KFacts.kpSz CFSG.LocalAnalysis.UniquenessCase.UCK.szOrder3Aut_holds hF)

theorem routeHostGoodBig_of_res1Pt
    (hres : Step155HostE0WRes1RPtBig Res1RoutePt) :
    RouteHostGoodBig := by
  intro G _ _ A b Lb hb h9Ω hpgl hm12 hj2 hW
  have hT := (hb.chosen136.2 b hb.zpowers_mem_omegaA Lb hb.mem_lA).1
  have hbL : b ∉ Lb ∧ Nat.card (A ⊓ Lb : Subgroup G) = 9 := by
    rcases Ronan148B.Res148BPoint.cases131_of_sec13Data Sec13.rank3II_13_1_holds hb.toSec13Data
        hT with ⟨hbL, h9, -⟩ | ⟨hbL, h9, -⟩ | hbad
    · exact ⟨hbL, h9⟩
    · exact ⟨hbL, h9⟩
    · exact absurd hbad.2.1 hpgl
  exact step155HostE0WBig_of_y1 Sec11.Close.closed_sec4Item4_1LargePrime
    Sec11.Close.closed_sec4Item4_1ThreeCover Sec11.Close.closed_sec4Item4_3
    Sylow155R1.coverInputs46_closed Ronan148M.concl142S14_holds Ronan149.item1444S14_holds
    (y1SecondFormExcl_of_k143Excl Sec11.Close.closed_sec4Item4_1LargePrime
      Sec11.Close.closed_sec4Item4_1ThreeCover Sec11.Close.closed_sec4Item4_3
      Sylow155R1.coverInputs46_closed
      (Sylow155L143.k143Excl_of_inputs Sec11.Close.closed_sec4Item4_1ThreeCover
        Sec11.Close.closed_sec4Item4_3 Sylow155R1.coverInputs46_closed))
    hb hW hbL.2 hbL.1 (hres G A b Lb hb (Or.inl ⟨h9Ω, hpgl, hm12, hj2⟩) hW)

theorem routeHostJ2LtBig_of_res1Pt
    (hres : Step155HostE0WRes1RPtBig Res1RoutePt) :
    RouteHostJ2LtBig := by
  intro G _ _ A b Lb hb h3 hJb
  obtain ⟨hbL, h9, -⟩ := Sec14.j2_point_facts hb.toSec13Data hJb
  have hW := normalizer_le_of_omegaA_eq
    (Gagen155Y1.omegaA_eq_singleton_of_j2_of_ncard_lt item134_holds Sec11.Close.closed_sec4Item4_8
      hb hJb h3)
  exact step155HostE0WBig_of_y1 Sec11.Close.closed_sec4Item4_1LargePrime
    Sec11.Close.closed_sec4Item4_1ThreeCover Sec11.Close.closed_sec4Item4_3
    Sylow155R1.coverInputs46_closed Ronan148M.concl142S14_holds Ronan149.item1444S14_holds
    (y1SecondFormExcl_of_k143Excl Sec11.Close.closed_sec4Item4_1LargePrime
      Sec11.Close.closed_sec4Item4_1ThreeCover Sec11.Close.closed_sec4Item4_3
      Sylow155R1.coverInputs46_closed
      (Sylow155L143.k143Excl_of_inputs Sec11.Close.closed_sec4Item4_1ThreeCover
        Sec11.Close.closed_sec4Item4_3 Sylow155R1.coverInputs46_closed))
    hb hW h9 hbL (hres G A b Lb hb (Or.inr ⟨h3, hJb⟩) hW)

theorem routeHostJ2SmallBig_of_lt
    (h : RouteHostJ2LtBig) : RouteHostJ2SmallBig := by
  intro G _ _ A b Lb hb h3 hJb
  rcases lt_or_eq_of_le h3 with h3 | h3
  · exact h G A b Lb hb h3 hJb
  · exact step155HostE0WBig_of (step155HostE0W_of_noG28 item134_holds
      Sec11.Close.closed_sec4Item4_8 Ronan148M.concl142S14_holds Ronan149.item1444S14_holds hb hJb
      h3 (Sylow155R3.step155NoG28WR_holds G A b Lb hb h3 hJb))

theorem item155wJ2R_of_bigHost
    (h316 : Sec19.Item316) (hJ : RouteHostJ2SmallBig)
    (hgood : RouteHostGoodBig) : Item155wJ2R := by
  have h131 := Sec13.rank3II_13_1_holds
  have h134 := item134_holds
  have h48 := Sec11.Close.closed_sec4Item4_8
  have h148 : Item148R := Ronan148M.item148R_holds
  have h149 : Sec16.Item149S14 := Ronan149.item149S14_holds
  have h146 : Item146S14 := Proof148FourK.item146S14_holds
  have h1444 : Item1444S14 := Ronan149.item1444S14_holds
  have hbot : Item145BotS14 := Ronan149.item145BotS14_holds
  have hst : StellmacherKP :=
    ⟨CFSG.RankThree.S4Free.Stell34.stellmacherSzAll_proved.{0, 0}, KFacts.kpSz⟩
  have h152 : Item152BigR := Ronan152Six.item152BigR_of
    Sec4.Census.rank3II_4_4_of_griess_noItem41
    (step152CompR_of_item148R h149 h148 h134 h48 Sec4.Sporadic.rank3II_4_15 KFacts.kpSz)
    (step152ExclR_of (step152ExclSL2_of_item148HJ h134 h48
      (item148HJS14_of_wired Ronan148M.item148S14_holds)))
  have hE0 : Step155HostE0WRBig := step155HostE0WRBig_of_t52_switch
    Sec11.Close.closed_sec4Item4_1LargePrime Sec11.Close.closed_sec4Item4_1ThreeCover
    Sec11.Close.closed_sec4Item4_3 Sylow155R1.coverInputs46_closed h131
    (rank3II_13_2_of h131 item4_22_holds Sec4.rank3II_4_5) h134 h48 Ronan148M.concl142S14_holds
    h1444 Ronan137H.item137_holds (claim1515M12_of (hK := KFacts.ks1515M12Cover) (h131 := h131))
    (item1511StarR_of_item1511R (Res1H1.item1511R_of_item316 h316))
    (Sec16.step1513MeetsPoint_of_steps148 (hCore := Ronan148C.step148Core_holds)
      (hPoint := Ronan148M.step148Point_holds) (hKT := Ronan148M.step148KType_holds))
    hJ hgood
  have hfr : Step155FrattiniNWPRBig := step155FrattiniNWPRBig_of_hostE0R hst h134 h48
    Ronan148M.item143QS14_holds h146 h148 h149 hE0
  exact Ronan155Big.item155wJ2R_of_item155wBigR (item155wBigR_of_corr8Cert_bigFr h152
    (Ronan153Big.item153BigR_of_closed item135_holds h316 h152)
    (Ronan154Big.item154PiR_of_item159R (Ronan154Big.item159R_of_big154 item135_holds h316 h152))
    item3_15_holds h316 h1444 h146 hbot h149 Ronan148M.concl142S14_holds h148 h134 h48
    CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS155.ks155J2CentE4 kSL3NonPiAutThree
    LiebeckClosed.step155UpPiNHJR_holds Ronan155Y.step155GrowAltTwoFieldWR_holds
    Proof148FourK.step155YQ0HypWR_holds Proof148FourK.step155PJQ0HypWR_holds
    Ronan155Y.y4LThreePiNHJR_holds
    (step155W315xR_of_P hst h146 h1444 h148 h149
      (Ronan155W315.step155W315PR_of_v4 KFacts.kpSz h148 Ronan148M.concl142S14_holds
        Ronan148M.concl143S14_holds h146 h1444 hbot h149 item142AllS14_holds h134 h48
        LiebeckClosed.y4CoreMemSolvR_holds))
    hfr)

theorem item155wJ2R_of_l3Pt
    (h316 : Sec19.Item316)
    (hL3 : Step155HostE0WRes1TypeFPt Res1L3Pt Res1OpenType)
    (hA7 : Step155HostE0WRes1TypeFBar (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7)))
      Res1OpenType)
    (hM22 : Step155HostE0WRes1TypeFBar
      (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) Res1OpenType) :
    Item155wJ2R := by
  have h152 : Item152BigR := Ronan152Six.item152BigR_of
    Sec4.Census.rank3II_4_4_of_griess_noItem41
    (step152CompR_of_item148R Ronan149.item149S14_holds Ronan148M.item148R_holds item134_holds
      Sec11.Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15 KFacts.kpSz)
    (step152ExclR_of (step152ExclSL2_of_item148HJ item134_holds Sec11.Close.closed_sec4Item4_8
      (item148HJS14_of_wired Ronan148M.item148S14_holds)))
  have h154 : Item154R := item154R_of_item154PiR
    (Ronan154Big.item154PiR_of_item159R (Ronan154Big.item159R_of_big154 item135_holds h316 h152))
  have hres : Step155HostE0WRes1RPtBig Res1RoutePt := step155HostE0WRes1RPtBig_of_res1OpenF
    (step155HostE0WRes1TypeFPtBig_route_of_l3Pt
      (Gagen155R1HJ.step155HostE0WRes1TypeFPtBig_j2 h154 h152
        (Ronan153Big.item153BigR_of_closed item135_holds h316 h152))
      hL3 hA7 hM22)
  exact item155wJ2R_of_bigHost h316 (routeHostJ2SmallBig_of_lt (routeHostJ2LtBig_of_res1Pt hres))
    (routeHostGoodBig_of_res1Pt hres)

theorem res1J2Item156_of_155w
    (h316 : Sec19.Item316) (h155 : Item155wJ2R) : Res1J2Item156 := by
  have h134 := item134_holds
  have h48 := Sec11.Close.closed_sec4Item4_8
  have h415 := Sec4.Sporadic.rank3II_4_15
  have h148 : Item148R := Ronan148M.item148R_holds
  have h149 : Sec16.Item149S14 := Ronan149.item149S14_holds
  have h152 : Item152BigR := Ronan152Six.item152BigR_of
    Sec4.Census.rank3II_4_4_of_griess_noItem41
    (step152CompR_of_item148R h149 h148 h134 h48 h415 KFacts.kpSz)
    (step152ExclR_of (step152ExclSL2_of_item148HJ h134 h48
      (item148HJS14_of_wired Ronan148M.item148S14_holds)))
  have h153 : Item153MainJ2R := Ronan153Big.item153MainJ2R_of_item153BigR
    (Ronan153Big.item153BigR_of_closed item135_holds h316 h152)
  exact Gagen155R1HJ.res1J2Item156_of h148 h134 h48 h415 item142AllS14_holds item1411_1R_holds
    (item152R_of_155w h155 claim1411LocalR_holds h152 h153 h149 h148 h134 h48 h415 KFacts.kpSz)
    (item153MainR_of_155w h155 claim1411LocalR_holds h152 h153 h316 h149 h148 h134 h48 h415
      KFacts.kpSz item135_holds Ronan137H.item137_holds item142AllS14_holds
      Ronan148M.concl142S14_holds Ronan148M.concl143S14_holds Proof148FourK.item146S14_holds
      Ronan149.item1444S14_holds Ronan149.item145BotS14_holds
      (item148HJS14_of_wired Ronan148M.item148S14_holds))
    (claim153ObsR_of_155w h155 claim1411LocalR_holds h152 h153 h316 h149 h148 h134 h48 h415
      KFacts.kpSz)

theorem step155HostE0WRes1TypeFPt_j2_of_l3Pt
    (h316 : Sec19.Item316)
    (hL3 : Step155HostE0WRes1TypeFPt Res1L3Pt Res1OpenType)
    (hA7 : Step155HostE0WRes1TypeFBar (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7)))
      Res1OpenType)
    (hM22 : Step155HostE0WRes1TypeFBar
      (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) Res1OpenType) :
    Step155HostE0WRes1TypeFPt Res1J2Pt Res1OpenType := by
  have h152 : Item152BigR := Ronan152Six.item152BigR_of
    Sec4.Census.rank3II_4_4_of_griess_noItem41
    (step152CompR_of_item148R Ronan149.item149S14_holds Ronan148M.item148R_holds item134_holds
      Sec11.Close.closed_sec4Item4_8 Sec4.Sporadic.rank3II_4_15 KFacts.kpSz)
    (step152ExclR_of (step152ExclSL2_of_item148HJ item134_holds Sec11.Close.closed_sec4Item4_8
      (item148HJS14_of_wired Ronan148M.item148S14_holds)))
  exact Gagen155R1HJ.step155HostE0WRes1TypeFPt_j2_of_156
    (item154R_of_item154PiR (Ronan154Big.item154PiR_of_item159R
      (Ronan154Big.item159R_of_big154 item135_holds h316 h152)))
    (res1J2Item156_of_155w h316 (item155wJ2R_of_l3Pt h316 hL3 hA7 hM22))

theorem item1730_of_l3Pt
    (h316 : Sec19.Item316) (h310 : Sec6.Item3_10)
    (hL3 : Step155HostE0WRes1TypeFPt Res1L3Pt Res1OpenType)
    (hA7 : Step155HostE0WRes1TypeFBar (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7)))
      Res1OpenType)
    (hM22 : Step155HostE0WRes1TypeFBar
      (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) Res1OpenType) :
    Sec17.Item1730 :=
  Sylow155R1.item1730_of_res1OpenFPt h316 h310
    (step155HostE0WRes1TypeFPt_route_of_l3Pt
      (step155HostE0WRes1TypeFPt_j2_of_l3Pt h316 hL3 hA7 hM22) hL3 hA7 hM22)

end CFSG.RankThree.PartTwo.Sec15
