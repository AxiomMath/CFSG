module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_L34Fix : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsL3 X 2 →
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) X V) (β : V →ₗ[ZMod 2] V),
    (∀ x : X, ρ x ∘ₗ β = β ∘ₗ ρ x) → β ^ 3 = 1 →
    (∀ W : Submodule (ZMod 2) V,
      (∀ x : X, W.map (ρ x) ≤ W) → W.map β ≤ W → W = ⊥ ∨ W = ⊤) →
    (∃ x : X, ∃ v : V, ρ x v ≠ v) →
    ∀ a : X, orderOf a = 3 → 4 ≤ Nat.card (LinearMap.ker (ρ a ∘ₗ β - 1))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
