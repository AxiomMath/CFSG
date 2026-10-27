module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155BigHostDefs
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJBigDefs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1PtL3
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Setup
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Types
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Mid
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cor141
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidL2Solv
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1OpenSolv
public import CFSG.RankThree.PartTwo.Sec4.Census.Open46

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem step155HostE0WRes1TypePtBig_of_field (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (h143 : Y1SecondFormExcl) (h142 : Concl142S14) (h1444 : Item1444S14) (hSz : KFacts.KPSz)
    (hSz3 : CFSG.LocalAnalysis.UniquenessCase.UCK.SzOrder3Aut)
    {Pt : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → Prop}
    {P : ∀ (Y : Type) [Group Y], Prop}
    (hP : ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → P Y → Res1AutSolv Y)
    (hF : Step155HostE0WRes1TypeFPtBig Pt P) : Step155HostE0WRes1TypePtBig Pt P := by
  intro G _ _ A c L hR hPt hN hS X K Y M T P' hC hXb hmax habove hE h146 hRP hIX Yc hY hsimple
    hPY
  have hEA := Sylow155R1.res1_layerOddPreimage_le_centralizer (h1444 G A c L hS) hSz hSz3 hS
    h146 hC hE hRP hIX
  have hEO := Sylow155R1.res1_layerOddPreimage_eq_of_autSolv h1 h2 h43 hin h143 hR hN
    (h142 G A c L hS) hC hE h146 hRP hIX hY hsimple (hP ↥Yc hsimple hPY) hEA
  rw [hEO]
  by_cases hfield : ∃ x : ↥(Res1C A L),
      (x : G) ∈ CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (A : Set G) ∧
        ∃ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x * y ≠
          y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x
  · exact hF G A c L hR hPt hN hS X K Y M T P' hC hXb hmax habove hE h146 hRP hIX Yc hY hsimple
      hPY hEA hEO (fun _ hu huY => Sylow155R1.res1_eq_one_of_mem_pPrimeCoreOf_two h1 h2 h43 hin
        h143 hR hN (h142 G A c L hS) hC hE h146 hRP hIX hY hsimple hEA hu huY) hfield
  · push Not at hfield
    exact Sylow155R1.res1_pPrimeCoreOf_le_of_comm h1 h2 h43 hin h143 hR hN (h142 G A c L hS) hC
      hE h146 hRP hIX hY hsimple hEA hfield

theorem step155HostE0WRes1TypePtBig_open_of_field (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (h143 : Y1SecondFormExcl) (h142 : Concl142S14) (h1444 : Item1444S14) (hSz : KFacts.KPSz)
    (hSz3 : CFSG.LocalAnalysis.UniquenessCase.UCK.SzOrder3Aut)
    {Pt : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → Prop}
    (hF : Step155HostE0WRes1TypeFPtBig Pt Res1OpenType) :
    Step155HostE0WRes1TypePtBig Pt Res1OpenType :=
  step155HostE0WRes1TypePtBig_of_field h1 h2 h43 hin h143 h142 h1444 hSz hSz3
    (fun _ _ _ _ hY => by
      rcases hY with ⟨n, hn0, -, ⟨e⟩⟩ | ⟨n, hn0, hneven, ⟨e⟩⟩
      · exact Res1AutSolv.of_mulEquiv e (Sylow155R1.res1AutSolv_projSL_two (by omega))
      · exact Res1AutSolv.of_mulEquiv e (Sylow155R1.res1AutSolv_projSU_three hneven hn0)) hF

theorem step155HostE0WRes1RPtBig_of_types
    {Pt : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → Prop}
    (hfact : Res1TypeFact)
    (hoddL2 : Step155HostE0WRes1Type Res1OddL2Type)
    (hoddL3 : Step155HostE0WRes1Type Res1OddL3Type) (hJ1 : Step155HostE0WRes1Type Res1J1Type)
    (hsmall : Step155HostE0WRes1Type Res1SmallType)
    (hL2odd : Step155HostE0WRes1Type Res1L2OddType)
    (hmid : Step155HostE0WRes1Type Res1MidType)
    (hopen : Step155HostE0WRes1TypePtBig Pt Res1OpenType) : Step155HostE0WRes1RPtBig Pt := by
  intro G _ _ A c L hR hPt hN hS X K Y M T P hctx hXb hmax habove hend h146 hYP hdelta hres
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
  · exact hopen G A c L hR hPt hN hS X K Y M T P hctx hXb hmax habove hend h146 hYP hdelta Yc
      hY hsimple h

theorem step155HostE0WRes1TypeFPtBig_route_of_l3Pt {P : ∀ (Y : Type) [Group Y], Prop}
    (hJ2 : Step155HostE0WRes1TypeFPtBig Res1J2Pt P)
    (hL3 : Step155HostE0WRes1TypeFPt Res1L3Pt P)
    (hA7 : Step155HostE0WRes1TypeFBar (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) P)
    (hM22 : Step155HostE0WRes1TypeFBar
      (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) P) :
    Step155HostE0WRes1TypeFPtBig Res1RoutePt P := by
  intro G _ _ A c L hR hPt hN hS X K Y M T P' hC hXb hmax habove hE h146 hRP hIX Yc hY hsimple
    hP hEA hEO hcomm hfield
  by_cases hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)
  · have hJPt : Res1J2Pt G A c L := by
      rcases hPt with ⟨-, -, -, h⟩ | h
      · exact (h.false hJ.some).elim
      · exact h
    exact hJ2 G A c L hR hJPt hN hS X K Y M T P' hC hXb hmax habove hE h146 hRP hIX Yc hY
      hsimple hP hEA hEO hcomm hfield
  have hgood : ¬ Sec8.IsZ3PGLThreePi (lBarA c L A) ∧
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) := by
    rcases hPt with ⟨-, h1, h2, -⟩ | ⟨-, h⟩
    · exact ⟨h1, h2⟩
    · exact absurd h hJ
  rcases barL_cases_of_sec15R hR with h | h | h | h | h
  · exact absurd h hJ
  · exact hL3 G A c L hR ⟨h, hgood.1⟩ hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY
      hsimple hP hEA hEO hcomm hfield
  · exact hA7 G A c L hR h hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
      hEA hEO hcomm hfield
  · exact hM22 G A c L hR h hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
      hEA hEO hcomm hfield
  · exact (hgood.2.false h.some).elim

end CFSG.RankThree.PartTwo.Sec15
