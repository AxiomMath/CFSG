module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

@[expose] def R922A5 (D : Data G) : Prop :=
  ∀ Y H D₃ S : Subgroup G, Hyp97 D Y H D₃ S → IsAlt (Bar2 (Opp 3 Y)) 5 → pCoreOf 2 Y ≠ ⊥ →
    ¬ IsSylowOf 2 S D.M → ¬ UC6.calCGS (pCoreOf 2 Y) ≤ D.M

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
