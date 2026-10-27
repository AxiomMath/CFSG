module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def KCentSz : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (a : ℕ), IsSz X a →
    ∀ θ : MulAut X, Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
      ∃ s : ℕ, s ∣ a ∧ a / s ∣ orderOf θ ∧
        (∃ x : X, orderOf x = 2 ^ s - 1 ∧ θ x = x) ∧
        (s = 1 → ∀ x ∈ Subgroup.normalizer ((S : Subgroup X) : Set X),
          θ x * x⁻¹ ∈ (S : Subgroup X) → x ∈ (S : Subgroup X))

@[expose] def KSzBorel : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (a : ℕ), IsSz X a →
    ∀ S : Sylow 2 X, ∃ D : Subgroup X, Nat.card D = 2 ^ a - 1 ∧
      D ≤ Subgroup.normalizer ((S : Subgroup X) : Set X)

@[expose] def KSzTwoAut : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (a : ℕ), IsSz X a →
    ∀ (S : Sylow 2 X) (θ : MulAut X), (∃ n : ℕ, orderOf θ = 2 ^ n) →
      (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
      ∃ s ∈ (S : Subgroup X), θ = MulAut.conj s

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
