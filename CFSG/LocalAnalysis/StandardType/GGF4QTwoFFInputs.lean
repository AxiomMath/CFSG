module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFStatement
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def FF81bG0Input :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 3 B Bs x L D J → GGSecFiveWeylCase 3 B Bs x D J →
    GGInnerDiagOnLabel GGLabQTwo 3 Bs L → ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
    GGWeylOfType 3 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
    (LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 5 ∧ lab.n = 1) ∨
      LargeEvenMarking ↥K (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 5 ∧ lab.n = 1)) →
    Nonempty (G ≃* (ggU .E6 0 1).K) → ggG0 3 B x L D J = ⊤

end CFSG.StandardType

end
