module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1PtDefs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1BarDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def Res1L3Pt (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
    (L : Subgroup G) : Prop :=
  IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∧ ¬ Sec8.IsZ3PGLThreePi (lBarA c L A)

theorem step155HostE0WRes1TypeFPt_route_of_l3Pt {P : ∀ (Y : Type) [Group Y], Prop}
    (hJ2 : Step155HostE0WRes1TypeFPt Res1J2Pt P) (hL3 : Step155HostE0WRes1TypeFPt Res1L3Pt P)
    (hA7 : Step155HostE0WRes1TypeFBar (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) P)
    (hM22 : Step155HostE0WRes1TypeFBar
      (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) P) :
    Step155HostE0WRes1TypeFPt Res1RoutePt P := by
  intro G _ _ A c L hR hPt hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
    hEA hEO hcomm hfield
  by_cases hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)
  · have hJPt : Res1J2Pt G A c L := by
      rcases hPt with ⟨-, -, -, h⟩ | h
      · exact (h.false hJ.some).elim
      · exact h
    exact hJ2 G A c L hR hJPt hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple
      hP hEA hEO hcomm hfield
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
