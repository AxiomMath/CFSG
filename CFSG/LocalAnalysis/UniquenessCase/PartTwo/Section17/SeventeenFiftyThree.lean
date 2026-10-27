module

public import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.RankTwoOuterRankHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

private theorem pRank_le_eM_of_prime {M : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p M ≤ eM M := by
  unfold eM
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card M, ?_⟩
    rintro n ⟨q, hq, hq2, rfl⟩
    exact CFSG.RankThreeEvenClassification.Helpers.pRank_le_card q hq M
  · exact ⟨p, hp, hp2, rfl⟩

section Certified


theorem seventeen_fiftythree (D : Data G) (V₀ V : Subgroup G)
    (h17_49 : R17_49At D V₀ V) (h17_50 : R17_50At D V₀ V)
    (h17_51 : R17_51At D V₀ V) (h17_52_1 : R17_52_1At D V₀ V)
    (h13 : SigmaRankThree13 D)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) :
    R17_53At D V₀ V := by
  intro L X p n l C Dc Gamma ctx r hr hr5 hrdvd
  by_contra hne
  have hLX : L = X := h17_49 L X p n l C Dc Gamma ctx
  subst hLX
  have h50 := (h17_50 L L p n l C Dc Gamma ctx).1
  have htype : LieModel (Bar2 L) .PSU 4 2 n ∨ LieModel (Bar2 L) .PSp 2 2 n ∨
      LieModel (Bar2 L) .G2 0 2 n := by
    rcases h50 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hm3 : 3 ≤ CFSG.Open.pRank r D.M :=
    Inputs1719.k_RankTwoOuterRank_holds D.M L n r ctx.mem_calC htype hr hr5 hrdvd hne
  have hp : p.Prime := (D.sig_prime p ctx.p_mem).1
  have hp2 : p ≠ 2 := (D.sig_prime p ctx.p_mem).2
  have heM : eM D.M = 3 := h17_52_1 L L p n l C Dc Gamma ctx
  have hr3 : CFSG.Open.pRank r D.M = 3 := by
    apply le_antisymm _ hm3
    have h := pRank_le_eM_of_prime (M := D.M) hr (by omega)
    rwa [heM] at h
  have hp3 : CFSG.Open.pRank p D.M = 3 := by
    apply le_antisymm _ (hSg.three_le p ctx.p_mem)
    have h := pRank_le_eM_of_prime (M := D.M) hp hp2
    rwa [heM] at h
  have hr7 : 7 ≤ r := by
    have h6 : r ≠ 6 := by rintro rfl; norm_num at hr
    omega
  have hrsig : r ∈ D.sig :=
    h13 ⟨p, ctx.p_mem, hp3⟩ r hr hr7 hr3.ge
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC ctx.mem_calC
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns hrsig
  have : Fact r.Prime := ⟨hr⟩
  let Q : Sylow r C := Sylow.nonempty.some
  let R : Subgroup G := (Q : Subgroup C).map C.subtype
  have hR : CFSG.ABGLocalTools.IsSylowOf r R C := ⟨Q, rfl⟩
  have hRC : R ≤ C := Subgroup.map_subtype_le _
  have hRgrp : IsPGroup r R := Q.isPGroup'.map C.subtype
  have hRM : R ≤ D.M := hRC.trans (ctx.cartan.1.trans ctx.mem_calC.1.le)
  exact h17_51 L L p n l C Dc Gamma ctx r hr hrdvd R hR
    (CFSG.RankThree.PartOne.IsStronglyPEmbedded.rankThreeGamma_one_le_of_le hsp hr hRgrp hRM)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
