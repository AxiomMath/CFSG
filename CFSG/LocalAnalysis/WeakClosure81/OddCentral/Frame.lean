module
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.SmithB42Sp4Desc
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open CFSG.Quasithin CFSG.Open Subgroup

@[expose] def IsFrame {Y : Type} [Group Y] (s d₁ d₂ d₃ t : Y) : Prop :=
  IsConj s d₁ ∧ IsConj s d₂ ∧ IsConj s d₃ ∧ Commute d₁ d₂ ∧ Commute d₂ d₃ ∧ Commute d₁ d₃ ∧
    d₁ * d₂ * d₃ ∈ fusionZStar Y ∧ d₁ * d₂ ∉ fusionZStar Y ∧
    t * d₁ * t⁻¹ = d₂ ∧ t * d₂ * t⁻¹ = d₃ ∧ t * d₃ * t⁻¹ = d₁

end CFSG.LocalAnalysis.WeakClosure81.OddCentral
