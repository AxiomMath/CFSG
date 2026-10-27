module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Late.Defs
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def Item182Alt1C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Sec18Std G A M →
    ∀ H ∈ scriptH A M, ∀ X : Subgroup G, H ≤ X → X ≠ ⊤ →
      ∀ c ∈ A, c ≠ 1 → Subgroup.centralizer ({c} : Set G) ≤ X →
        c ∈ sectionCentralizer A (inSubgroup perfectResidual H)
          (CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H)) →
        ∃ K ∈ oTwoComponentsIn X, K = inSubgroup perfectResidual H ⊔ CFSG.Open.pCoreOf 2 K

end CFSG.RankThree.PartTwo.Sec18
