module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJBigDefs
public import CFSG.RankThree.PartTwo.Sec15.Ronan155BigTools
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJDefs
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJNotLeDefs
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJNotLeRead
public import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Omega
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T112

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15

section InPt


theorem res1L112InPt_j2_big_of_j2K (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148R)
    (h142 : Item142R) (hθS : HJThetaS14) (hK : Res1L112InPtJ2K Res1J2Pt Res1OpenType)
    (h156 : Res1J2Item156Big) (hX1 : Res1J2X1) :
    Res1L112InPtBig Res1J2Pt Res1OpenType := by
  intro G _ _ A c L hR hPt hN hS X K Y M T P' hC hXb hmax habove hE h146 hRP hIX Yc hY hsimple
    hP hEA hEO hcomm hfield hLX
  have hJ := hPt.2
  have hΩ := Gagen155Y1.omegaA_eq_singleton_of_j2_of_ncard_lt h134 h48 hR hJ hPt.1
  rcases hj_read148_of_omegaA_eq h148 h134 h48 h142 hR hJ (hθS G A c L hS hJ) hΩ
      hC.mem_k.prop.1 with ht | h7 | h37 | ⟨hKJ, -⟩
  · exfalso
    obtain ⟨h5, h6, hON⟩ := h156 G A c L hR hJ hΩ K hC.mem_k (Ronan155Big.big152_k hC hXb)
    rcases ht with he | h6' | hON'
    · exact h5.false he.some
    · exact h6 h6'
    · exact hON hON'
  · exact ((hX1 G A c L hR hJ hΩ K hC.mem_k).1.false h7.some).elim
  · exact ((hX1 G A c L hR hJ hΩ K hC.mem_k).2 h37).elim
  · exact hK G A c L hR hPt hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
      hEA hEO hcomm hfield hKJ hLX

end InPt

theorem step155HostE0WRes1TypeFPtBig_of_le_of_in
    (h149 : Sec16.Item149S14)
    {Q : ∀ (X : Type) [Group X], Prop}
    {Pt : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → Prop}
    {P : ∀ (Y : Type) [Group Y], Prop}
    (hPQ : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Pt G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hle : Step155HostE0WRes1TypeFBarLe Q P) (hin : Res1L112InPtBig Pt P) :
    Step155HostE0WRes1TypeFPtBig Pt P := by
  intro G _ _ A c L hR hPt hN hS X K Y M T P' hC hXb hmax habove hE h146 hRP hIX Yc hY hsimple
    hP hEA hEO hcomm hfield
  by_cases hLX : L ≤ X
  · exact hle G A c L hR (hPQ G A c L hPt) hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc
      hY hsimple hP hEA hEO hcomm hfield hLX
  · obtain ⟨hLΔ, hLK, hKL, hUK⟩ := hin G A c L hR hPt hN hS X K Y M T P' hC hXb hmax habove hE
      h146 hRP hIX Yc hY hsimple hP hEA hEO hcomm hfield hLX
    exact Sylow155R1.pPrimeCoreOf_two_host_le_n155_of_not_le hR h146 (h149 G A c L hS) hC
      habove hE hRP hIX (hEO.symm.le.trans hEA) hLX (Sec16.eq_oPrimeResidualOf_of_sec15R hR).le
      hLΔ hLK hKL hUK

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
