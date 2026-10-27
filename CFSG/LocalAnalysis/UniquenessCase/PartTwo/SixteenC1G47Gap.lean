module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47GapBot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47GapNe

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem r16_47_gap_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (hkit : OmegaKit)
    (h41 : R16_41 D) (h45b : R16_45b D) (h46 : R16_46 D) : R16_47_gap D := by
  intro V₀ V L hV hS hc hL hU4 x hx h47 h47a
  exfalso
  have ctx : G47Ctx D V₀ V L hV x := G47Ctx.of_l45b h45b hS hc hx
  have h3σ : 3 ∈ D.sig := by rw [hc.2.2.1]; simp
  have hsp : IsStronglyPEmbedded 3 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) h3σ
  have h46' : Concl1646 L x.val := h46 V₀ V L hV hS hc hL hU4 x hx
  by_cases hne : V₀ = ⊥
  · subst hne
    exact s16c1_G47_gap_bot D hkit h41 hsp hL ctx h46' h47 h47a
  · exact s16c1_G47_gap_ne D hsp hL ctx h46' h47 hne (h47a.2 hne)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
