module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1PtDefs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Route
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Setup
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Main
import CFSG.LocalAnalysis.UniquenessCase.UC1K45SzAut
import CFSG.RankThree.PartTwo.Sec15.Gagen155Y143
import CFSG.RankThree.PartTwo.Sec15.Sylow155L143Holds
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Types
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Fact
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Bal
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cor141
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Mid
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidL2Solv
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1OpenSolv
import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Route
import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Omega
public import CFSG.RankThree.PartTwo.Sec14.Ronan143QRouteLeaves5b

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem step155HostE0WRes1TypePt_of_field (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (h143 : Y1SecondFormExcl) (h142 : Concl142S14) (h1444 : Item1444S14) (hSz : KFacts.KPSz)
    (hSz3 : CFSG.LocalAnalysis.UniquenessCase.UCK.SzOrder3Aut)
    {Pt : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → Prop}
    {P : ∀ (Y : Type) [Group Y], Prop}
    (hP : ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → P Y → Res1AutSolv Y)
    (hF : Step155HostE0WRes1TypeFPt Pt P) : Step155HostE0WRes1TypePt Pt P := by
  intro G _ _ A c L hR hPt hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hPY
  have hEA := res1_layerOddPreimage_le_centralizer (h1444 G A c L hS) hSz hSz3 hS h146 hC hE hRP
    hIX
  have hEO := res1_layerOddPreimage_eq_of_autSolv h1 h2 h43 hin h143 hR hN (h142 G A c L hS) hC
    hE h146 hRP hIX hY hsimple (hP ↥Yc hsimple hPY) hEA
  rw [hEO]
  by_cases hfield : ∃ x : ↥(Res1C A L),
      (x : G) ∈ CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (A : Set G) ∧
        ∃ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x * y ≠
          y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x
  · exact hF G A c L hR hPt hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hPY
      hEA hEO (fun _ hu huY => res1_eq_one_of_mem_pPrimeCoreOf_two h1 h2 h43 hin h143 hR hN
        (h142 G A c L hS) hC hE h146 hRP hIX hY hsimple hEA hu huY) hfield
  · push_neg at hfield
    exact res1_pPrimeCoreOf_le_of_comm h1 h2 h43 hin h143 hR hN (h142 G A c L hS) hC hE h146 hRP
      hIX hY hsimple hEA hfield

theorem step155HostE0WRes1TypePt_open_of_field (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (h143 : Y1SecondFormExcl) (h142 : Concl142S14) (h1444 : Item1444S14) (hSz : KFacts.KPSz)
    (hSz3 : CFSG.LocalAnalysis.UniquenessCase.UCK.SzOrder3Aut)
    {Pt : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → Prop}
    (hF : Step155HostE0WRes1TypeFPt Pt Res1OpenType) : Step155HostE0WRes1TypePt Pt Res1OpenType :=
  step155HostE0WRes1TypePt_of_field h1 h2 h43 hin h143 h142 h1444 hSz hSz3 (fun _ _ _ _ hY => by
    rcases hY with ⟨n, hn0, -, ⟨e⟩⟩ | ⟨n, hn0, hneven, ⟨e⟩⟩
    · exact Res1AutSolv.of_mulEquiv e (res1AutSolv_projSL_two (by omega))
    · exact Res1AutSolv.of_mulEquiv e (res1AutSolv_projSU_three hneven hn0)) hF

theorem step155HostE0WRes1RPt_of_types
    {Pt : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → Prop}
    (hfact : Res1TypeFact)
    (hoddL2 : Step155HostE0WRes1Type Res1OddL2Type)
    (hoddL3 : Step155HostE0WRes1Type Res1OddL3Type) (hJ1 : Step155HostE0WRes1Type Res1J1Type)
    (hsmall : Step155HostE0WRes1Type Res1SmallType)
    (hL2odd : Step155HostE0WRes1Type Res1L2OddType)
    (hmid : Step155HostE0WRes1Type Res1MidType)
    (hopen : Step155HostE0WRes1TypePt Pt Res1OpenType) : Step155HostE0WRes1RPt Pt := by
  intro G _ _ A c L hR hPt hN hS X K Y M T P hctx hmax habove hend h146 hYP hdelta hres
  obtain ⟨Yc, hY⟩ := res1At_iff.mp hres
  obtain ⟨hhyp, hfree, -, hcomp, -⟩ := id hY
  obtain ⟨hsimple, htype⟩ := hfact G A c L Yc hS hhyp hfree hcomp
  rcases res1_type_cases htype with h | h | h | h | h | h | h
  · exact hoddL2 G A c L hR hN hS X K Y M T P hctx hmax habove hend h146 hYP hdelta Yc hY
      hsimple h
  · exact hoddL3 G A c L hR hN hS X K Y M T P hctx hmax habove hend h146 hYP hdelta Yc hY
      hsimple h
  · exact hJ1 G A c L hR hN hS X K Y M T P hctx hmax habove hend h146 hYP hdelta Yc hY hsimple h
  · exact hsmall G A c L hR hN hS X K Y M T P hctx hmax habove hend h146 hYP hdelta Yc hY
      hsimple h
  · exact hL2odd G A c L hR hN hS X K Y M T P hctx hmax habove hend h146 hYP hdelta Yc hY
      hsimple h
  · exact hmid G A c L hR hN hS X K Y M T P hctx hmax habove hend h146 hYP hdelta Yc hY
      hsimple h
  · exact hopen G A c L hR hPt hN hS X K Y M T P hctx hmax habove hend h146 hYP hdelta Yc hY
      hsimple h

section Certified

theorem step155HostE0WRes1RPt_of_res1OpenF
    {Pt : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → Prop}
    (hF : Step155HostE0WRes1TypeFPt Pt Res1OpenType) : Step155HostE0WRes1RPt Pt :=
  have h143 : Y1SecondFormExcl :=
    y1SecondFormExcl_of_k143Excl Sec11.Close.closed_sec4Item4_1LargePrime
      Sec11.Close.closed_sec4Item4_1ThreeCover Sec11.Close.closed_sec4Item4_3
      coverInputs46_closed
      (Sylow155L143.k143Excl_of_inputs Sec11.Close.closed_sec4Item4_1ThreeCover
        Sec11.Close.closed_sec4Item4_3 coverInputs46_closed)
  step155HostE0WRes1RPt_of_types (res1TypeFact_of Sec11.Close.closed_sec4Item4_1LargePrime)
    step155HostE0WRes1Type_oddL2 step155HostE0WRes1Type_oddL3 step155HostE0WRes1Type_j1
    step155HostE0WRes1Type_small step155HostE0WRes1Type_l2Odd
    (step155HostE0WRes1Type_mid Sec11.Close.closed_sec4Item4_1LargePrime
      Sec11.Close.closed_sec4Item4_1ThreeCover Sec11.Close.closed_sec4Item4_3
      coverInputs46_closed h143 Ronan148M.concl142S14_holds Ronan149.item1444S14_holds)
    (step155HostE0WRes1TypePt_open_of_field Sec11.Close.closed_sec4Item4_1LargePrime
      Sec11.Close.closed_sec4Item4_1ThreeCover Sec11.Close.closed_sec4Item4_3
      coverInputs46_closed h143 Ronan148M.concl142S14_holds Ronan149.item1444S14_holds
      KFacts.kpSz CFSG.LocalAnalysis.UniquenessCase.UCK.szOrder3Aut_holds hF)

theorem routeHostGood_of_res1Pt
    (hres : Step155HostE0WRes1RPt Res1RoutePt) :
    Ronan143Q.RouteHostGood := by
  intro G _ _ A b Lb hb h9Ω hpgl hm12 hj2 hW
  have hT := (hb.chosen136.2 b hb.zpowers_mem_omegaA Lb hb.mem_lA).1
  have hbL : b ∉ Lb ∧ Nat.card (A ⊓ Lb : Subgroup G) = 9 := by
    rcases Ronan148B.Res148BPoint.cases131_of_sec13Data Sec13.rank3II_13_1_holds hb.toSec13Data
        hT with ⟨hbL, h9, -⟩ | ⟨hbL, h9, -⟩ | hbad
    · exact ⟨hbL, h9⟩
    · exact ⟨hbL, h9⟩
    · exact absurd hbad.2.1 hpgl
  exact step155HostE0W_of_y1 Sec11.Close.closed_sec4Item4_1LargePrime
    Sec11.Close.closed_sec4Item4_1ThreeCover Sec11.Close.closed_sec4Item4_3 coverInputs46_closed
    Ronan148M.concl142S14_holds Ronan149.item1444S14_holds
    (y1SecondFormExcl_of_k143Excl Sec11.Close.closed_sec4Item4_1LargePrime
      Sec11.Close.closed_sec4Item4_1ThreeCover Sec11.Close.closed_sec4Item4_3
      coverInputs46_closed
      (Sylow155L143.k143Excl_of_inputs Sec11.Close.closed_sec4Item4_1ThreeCover
        Sec11.Close.closed_sec4Item4_3 coverInputs46_closed))
    hb hW hbL.2 hbL.1 (hres G A b Lb hb (Or.inl ⟨h9Ω, hpgl, hm12, hj2⟩) hW)

theorem routeHostJ2Lt_of_res1Pt
    (hres : Step155HostE0WRes1RPt Res1RoutePt) :
    Ronan143Q.RouteHostJ2Lt := by
  intro G _ _ A b Lb hb h3 hJb
  obtain ⟨hbL, h9, -⟩ := Sec14.j2_point_facts hb.toSec13Data hJb
  have hW := normalizer_le_of_omegaA_eq
    (Gagen155Y1.omegaA_eq_singleton_of_j2_of_ncard_lt item134_holds Sec11.Close.closed_sec4Item4_8
      hb hJb h3)
  exact step155HostE0W_of_y1 Sec11.Close.closed_sec4Item4_1LargePrime
    Sec11.Close.closed_sec4Item4_1ThreeCover Sec11.Close.closed_sec4Item4_3 coverInputs46_closed
    Ronan148M.concl142S14_holds Ronan149.item1444S14_holds
    (y1SecondFormExcl_of_k143Excl Sec11.Close.closed_sec4Item4_1LargePrime
      Sec11.Close.closed_sec4Item4_1ThreeCover Sec11.Close.closed_sec4Item4_3
      coverInputs46_closed
      (Sylow155L143.k143Excl_of_inputs Sec11.Close.closed_sec4Item4_1ThreeCover
        Sec11.Close.closed_sec4Item4_3 coverInputs46_closed))
    hb hW h9 hbL (hres G A b Lb hb (Or.inr ⟨h3, hJb⟩) hW)

theorem item1730_of_res1OpenFPt
    (h316 : Sec19.Item316) (h310 : Sec6.Item3_10)
    (hF : Step155HostE0WRes1TypeFPt Res1RoutePt Res1OpenType) : Sec17.Item1730 :=
  Ronan143Q.item1730_of_routeS16_leaves5b h316 h310
    (routeHostJ2Lt_of_res1Pt (step155HostE0WRes1RPt_of_res1OpenF hF))
    (routeHostGood_of_res1Pt (step155HostE0WRes1RPt_of_res1OpenF hF))

end Certified

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
