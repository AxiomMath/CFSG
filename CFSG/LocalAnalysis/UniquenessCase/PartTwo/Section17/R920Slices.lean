module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

@[expose] def R920L2E (D : Data G) : Prop :=
  ∀ (L D₃ : Subgroup G) (n : ℕ), L ∈ calC D.M → D₃ ≤ L → Nat.card D₃ = 3 →
    D₃ ∈ uniqueSet D.M → IsL2 (Bar2 L) n →
    (∀ A : Subgroup G, A ≤ L → (Nat.card A).Prime → Nat.card A ≠ 2 →
      normalizer (A : Set G) ≤ D.M) →
    (∃ p ∈ D.sig, p ∣ Nat.card L) →
    (Even n ∨ ((∃ A : Subgroup G, A ∈ uniqueSet D.M ∧ A ≤ L ∧ (Nat.card A).Prime ∧
      Nat.card A ∣ 2 ^ n - 1) ∧ ∃ p ∈ D.sig, p ∣ 2 ^ n + 1)) →
    UniqueMax D.M L ∨ IsAlt (Bar2 L) 5

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
