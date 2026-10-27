module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFStatement
public import CFSG.LocalAnalysis.StandardType.GGF4QTwoFFInputs
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGStdSpSixExcl
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def GGF4QTwoEndsLInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 3 B Bs x L D J → GGSecFiveWeylCase 3 B Bs x D J →
    GGInnerDiagOnLabel GGLabQTwo 3 Bs L → ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
    GGWeylOfType 3 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      GGInnerDiagOnLabel GGLabSp6 3 Bs L ∨
      (∃ n : ℕ, (n = 5 ∨ n = 6) ∧
        LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = n ∧ lab.n = 1)) ∨
      LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1)

@[expose] def GGF4QTwoEndsKInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 3 B Bs x L D J → GGSecFiveWeylCase 3 B Bs x D J →
    GGInnerDiagOnLabel GGLabQTwo 3 Bs L → ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
    GGWeylOfType 3 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
    LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1) →
      LargeEvenMarking ↥K (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 5 ∧ lab.n = 1)

@[expose] def GGF4QTwoEndsKlInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 3 B Bs x L D J → GGSecFiveWeylCase 3 B Bs x D J →
    GGInnerDiagOnLabel GGLabQTwo 3 Bs L → ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
    GGWeylOfType 3 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
    LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1) →
      LargeEvenMarking ↥K (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 5 ∧ lab.n = 1) ∨
      LargeEvenMarking ↥K (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1)

end CFSG.StandardType

end
