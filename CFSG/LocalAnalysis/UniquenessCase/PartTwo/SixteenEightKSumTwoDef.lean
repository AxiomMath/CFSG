module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Background.B4Models
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

@[expose] def S16kPairFix (D₁ D₂ : FFModel) {X : Type} [Group X] (π₁ : D₁.Gam →* X)
    (π₂ : D₂.Gam →* X) (p : ℕ) : Prop :=
  ∀ (m₁ : ↥D₁.sec) (m₂ : ↥D₂.sec), ((m₁ : D₁.Amb) ∉ D₁.ker ∨ (m₂ : D₂.Amb) ∉ D₂.ker) →
    ∃ B : Subgroup X, IsPGroup p B ∧ ¬ IsCyclic ↥B ∧ ∀ b ∈ B,
      (∃ γ : D₁.Gam, π₁ γ = b ∧ D₁.act γ (m₁ : D₁.Amb) * (m₁ : D₁.Amb)⁻¹ ∈ D₁.ker) ∧
      (∃ γ : D₂.Gam, π₂ γ = b ∧ D₂.act γ (m₂ : D₂.Amb) * (m₂ : D₂.Amb)⁻¹ ∈ D₂.ker)

@[expose] def S16kModelsEquivVia (D₁ : FFModel) (act' : D₁.Gam → D₁.Amb → D₁.Amb) (D₂ : FFModel)
    {X : Type} [Group X] (π₁ : D₁.Gam →* X) (π₂ : D₂.Gam →* X) : Prop :=
  ∃ A : D₁.Amb ≃* D₂.Amb, (∀ m, m ∈ D₁.sec ↔ A m ∈ D₂.sec) ∧ (∀ m, m ∈ D₁.ker ↔ A m ∈ D₂.ker) ∧
    ∀ (γ₁ : D₁.Gam) (γ₂ : D₂.Gam), π₁ γ₁ = π₂ γ₂ → ∀ m, A (act' γ₁ m) = D₂.act γ₂ (A m)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
