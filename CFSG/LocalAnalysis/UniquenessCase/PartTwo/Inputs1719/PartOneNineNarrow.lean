module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def R9_14S (D : Data G) : Prop :=
  ∀ (Y H D₃ S : Subgroup G), Hyp97 D Y H D₃ S →
    ∀ S₀ : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S₀ H → S₀ ≤ D.M →
    ∀ (A B : Subgroup G) [(B.subgroupOf A).Normal],
      CFSG.SignalizerFunctorTheorem.McBride.Near.IsChiefFactorOf H A B →
      A ≤ PPrimeCoreIn 3 H →
      ¬ Group.IsSolvable (↥A ⧸ B.subgroupOf A) →
        A = (A ⊓ D.M) ⊔ B

@[expose] def R9_22sp5 (D : Data G) : Prop :=
  IsStronglyPEmbedded 5 D.M →
    ∀ (Y H D₃ S : Subgroup G), Hyp97 D Y H D₃ S → pCoreOf 2 Y ≠ ⊥ →
      IsAlt (Bar2 (Opp 3 Y)) 5 → H = (H ⊓ D.M) ⊔ PPrimeCoreIn 3 H

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
