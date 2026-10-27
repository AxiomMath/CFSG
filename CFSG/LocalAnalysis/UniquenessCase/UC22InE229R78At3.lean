module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (IrrOnMod)

variable {G : Type} [Group G] [Finite G]

@[expose] def R7_8At3 (D : Data G) : Prop :=
  ∀ H P D₀ : Subgroup G, Sec7Hyp D 3 H → CFSG.ABGLocalTools.IsSylowOf 3 P (H ⊓ D.M) →
    D₀ = CFSG.RankThree.PartOne.omegaOne 3 P →
      (∀ x ∈ D₀, x ^ 3 = 1) ∧
        ((H ⊓ D.M = H ⊓ normalizer (P : Set G) ∧
            IrrOnMod (rankThreeLayer H ⊓ normalizer (P : Set G)) D₀ (inSubgroup frattini D₀) ∧
            P = D₀) ∨
          (IsReeType (LKQuot7 3 H) 1 ∧
            ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M) ∧
              S ≤ normalizer (D₀ : Set G) ∧ IsCyclic S ∧ S ≤ rankThreeLayer (Opp 3 H) ∧
                S ≤ centralizer (PPrimeCoreIn 3 H : Set G)))

end CFSG.LocalAnalysis.UniquenessCase.UC22
