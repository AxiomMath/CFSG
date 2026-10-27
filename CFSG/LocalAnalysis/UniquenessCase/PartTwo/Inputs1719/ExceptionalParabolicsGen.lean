module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.F1Models
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

@[expose] def K_TitsParabolicGen : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieModel X .Tits 0 2 1 →
    ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ∃ P₁ P₂ : Subgroup X, S ≤ P₁ ∧ S ≤ P₂ ∧
      Nat.card P₁ = 3 * Nat.card S ∧ Nat.card P₂ = 5 * Nat.card S ∧ P₁ ⊔ P₂ = ⊤ ∧
      ∀ α : MulAut X, S.map α.toMonoidHom = S →
        P₁.map α.toMonoidHom = P₁ ∧ P₂.map α.toMonoidHom = P₂

@[expose] def K_2F4ParabolicGen : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), CFSG.Quasithin.Is2F4 n X →
    ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ∃ Y₁ Y₂ : Subgroup X,
      ⁅Y₁, Y₁⁆ = Y₁ ∧ ⁅Y₂, Y₂⁆ = Y₂ ∧ IsSz (Bar2 Y₁) n ∧ IsL2 (Bar2 Y₂) n ∧
      Y₁ ⊔ Y₂ ⊔ S = ⊤ ∧
      ∀ α : MulAut X, S.map α.toMonoidHom = S →
        Y₁.map α.toMonoidHom = Y₁ ∧ Y₂.map α.toMonoidHom = Y₂

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
