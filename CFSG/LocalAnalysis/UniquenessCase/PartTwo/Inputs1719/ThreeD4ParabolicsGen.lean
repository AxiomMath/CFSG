module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.F1Models
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

@[expose] def K_3D4ParabolicGen : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → Is3D4 X n →
    ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ∃ Y₁ Y₂ : Subgroup X,
      ⁅Y₁, Y₁⁆ = Y₁ ∧ ⁅Y₂, Y₂⁆ = Y₂ ∧ IsL2 (Bar2 Y₁) (3 * n) ∧ IsL2 (Bar2 Y₂) n ∧
      Y₁ ⊔ Y₂ ⊔ S = ⊤ ∧
      ∀ α : MulAut X, S.map α.toMonoidHom = S →
        Y₁.map α.toMonoidHom = Y₁ ∧ Y₂.map α.toMonoidHom = Y₂

@[expose] def K_3D4TwoParabolicGen : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Is3D4 X 1 →
    ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ∃ Y₁ X₂ : Subgroup X,
      ⁅Y₁, Y₁⁆ = Y₁ ∧ IsL2 (Bar2 Y₁) 3 ∧ S ≤ X₂ ∧ Nat.card X₂ = 3 * Nat.card S ∧
      Y₁ ⊔ X₂ = ⊤ ∧
      ∀ α : MulAut X, S.map α.toMonoidHom = S →
        Y₁.map α.toMonoidHom = Y₁ ∧ X₂.map α.toMonoidHom = X₂

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
