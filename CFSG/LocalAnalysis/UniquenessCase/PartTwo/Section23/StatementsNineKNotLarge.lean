module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def KNotLarge23 : Prop :=
  (∀ (Q : Type) [Group Q] [Finite Q],
    ((∃ a : ℕ, IsL2 Q a ∨ IsSz Q a) ∨
        (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsL2Odd Q q) ∨ IsJ1 Q) →
      ∀ (N : Subgroup Q) [N.Normal], ∀ n : ℕ, 3 ≤ n →
        ¬ (IsSLn (Q ⧸ N) 3 n ∨ IsSp4 (Q ⧸ N) n ∨ IsU4 (Q ⧸ N) n)) ∧
  (∀ (X : Type) [Group X] [Finite X] (n : ℕ), 3 ≤ n → IsL2Square X n →
    ¬ (IsSLn X 3 n ∨ IsSp4 X n ∨ IsU4 X n))

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
