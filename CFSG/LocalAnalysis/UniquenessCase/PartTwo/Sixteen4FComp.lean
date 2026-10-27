module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FCompDelta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UNt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34ThreeMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Thirteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16f_hyp154_of_nonthin (D : Data G) (S : s16h_Std D) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    (hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (lBar V₀ V h.hyp151.isElemAbelian L))
    (hδ : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 →
      delta15 D.M V₀ V h.hyp151.isElemAbelian L <
        gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1) :
    Hyp154 D V₀ V L := by
  obtain ⟨q, hq, hq2, hr⟩ := hnt
  have hσ₁ : ∃ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M := by
    obtain ⟨p, hp⟩ := S.hx.sig_nonempty
    exact ⟨p, hp, S.hSig.three_le p hp⟩
  exact s16h_hyp154_of_condU D S.h61 h hσ₁
    (s16h_condU_of_not_thin D S.h127 S.h119 S.h869 h hcomp hq hq2 hr) hs hδ

theorem r16_3FComp_of_fix_half (D : Data G) (S : s16h_Std D) (hK : K_NonthinFixHalfRows)
    (h1217 : R1217 D) (h153 : R15_3Small D) (h15_13 : R15_13Small D) : R16_3FComp D := by
  intro V₀ V L hV hS hc hs hcomp hnt
  have hL : barSub V₀ V hV L ≠ ⊥ := by
    haveI := hcomp.2.2.2
    have hnt' : Nontrivial ↥(lBar V₀ V hV L) :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥(lBar V₀ V hV L))).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt'
  by_cases hγ : gamma15 D.M V₀ V hV L ≤ 3
  · exact concl163F_of_concl163 hS hL hc
      (r16_3_four_gamma_le_three D S.hx S.h61 S.h127 h1217 h153 hS hL hc hγ)
  · exfalso
    have hγ4 : 4 ≤ gamma15 D.M V₀ V hV L := by omega
    have h154 : Hyp154 D V₀ V L := s16f_hyp154_of_nonthin D S hS hs hcomp hnt
      (fun _ => s16f_delta_lt_of_nonthin hK D hS hc hnt hγ4)
    have := h15_13 V₀ V L h154 hS.hyp16.small hL
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
