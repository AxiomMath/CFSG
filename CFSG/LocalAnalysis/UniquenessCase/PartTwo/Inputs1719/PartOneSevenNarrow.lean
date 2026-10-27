module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07

variable {G : Type} [Group G] [Finite G]

@[expose] def R7_8At5 (D : Data G) : Prop :=
  ∀ H P D₀ : Subgroup G, Sec7Hyp D 5 H → CFSG.ABGLocalTools.IsSylowOf 5 P (H ⊓ D.M) →
    D₀ = CFSG.RankThree.PartOne.omegaOne 5 P →
      (IrrOnMod (H ⊓ normalizer (P : Set G)) D₀ (inSubgroup frattini D₀) ∧ P = D₀) ∨
        (∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M) ∧ IsCyclic S) ∨
        S17.IsA5xA5 ↥(Opp 5 (H ⊓ D.M))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
