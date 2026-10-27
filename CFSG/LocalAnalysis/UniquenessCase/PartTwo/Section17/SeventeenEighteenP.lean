module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEighteenResidual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_18P_unless (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L →
    2 < CFSG.Open.pRank 3 (UC22.conjClosure D.M L) →
      CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M →
        ((L.subgroupOf D.M).Normal ∧ IsSpor (BarInf L) .ONan) ∨
          ∃ X : Subgroup G, F11.InP11 D X

section Certificates


theorem gap17_18P_unless_of_gap (D : Data G) (V₀ V : Subgroup G)
    (hKS1 : Inputs1719.K_SporadicThreePermuting) (hP : Gap17_18P D V₀ V) :
    Gap17_18P_unless D V₀ V := by
  intro L c h3 hstr
  by_cases h2 : CFSG.Open.pRank 3 L ≤ 2
  · exact Or.inr ((hP L c h3 hstr).1 h2)
  · push Not at h2
    by_cases hON : IsSpor (BarInf L) .ONan
    · by_cases hN : (L.subgroupOf D.M).Normal
      · exact Or.inl ⟨hN, hON⟩
      · exact Or.inr ((hP L c h3 hstr).2 hON hN)
    · exact Or.inr (exists_inP11_of_three_rank_gt_two D V₀ V
        (Inputs1719.k_SporadicThreePermutingLe_of hKS1 _) hstr c h2 hON)

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
