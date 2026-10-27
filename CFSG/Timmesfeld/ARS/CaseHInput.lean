module

public import CFSG.Timmesfeld.RankTwo.Presentation
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.ARS.CaseHMoufang

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType CFSG.LieType.Steinberg CFSG.Blueprint CFSG.Timmesfeld

@[expose] def G2Frame (G : Type) [Group G] (f : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ f ∧
    ∃ φ : ∀ γ, (Adjoint.g2Datum F).rootGroup γ → G,
      ConeCompatible (Steinberg.RootSystem.ofCartan (Adjoint.g2Datum F).isFiniteType
        (Adjoint.g2Datum F).divisible) (Adjoint.g2Datum F).rootGroup φ ∧
      Subgroup.closure (⋃ γ ∈ (Adjoint.g2Datum F).roots, Set.range (φ γ)) = ⊤ ∧
      ∃ γ ∈ (Adjoint.g2Datum F).roots, ∃ x, φ γ x ≠ 1

@[expose] def TwistedD4Frame (G : Type) [Group G] (f : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ f) ^ 3 ∧
    ∃ σ : F →+* F, (∀ c, σ c = c ^ 2 ^ f) ∧
    ∃ φ : ∀ γ, (TwistedD4.twistedDatum σ).rootGroup γ → G,
      ConeCompatible (Steinberg.RootSystem.ofCartan (TwistedD4.twistedDatum σ).isFiniteType
        (TwistedD4.twistedDatum σ).divisible) (TwistedD4.twistedDatum σ).rootGroup φ ∧
      Subgroup.closure (⋃ γ ∈ (TwistedD4.twistedDatum σ).roots, Set.range (φ γ)) = ⊤ ∧
      ∃ γ ∈ (TwistedD4.twistedDatum σ).roots, ∃ x, φ γ x ≠ 1

@[expose] def CaseHFrameInput : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → SigmaEqLambda R → MTransitive R →
    ∀ A ∈ R, 3 ≤ (linesThrough R A).ncard →
      ¬ (Nat.card A = 2 ∧ (linesThrough R A).ncard = 3) →
      (∃ f, 2 ≤ f ∧ Nat.card A = 2 ^ f ∧ G2Frame G f) ∨
        (∃ f, 1 ≤ f ∧ Nat.card A = 2 ^ f ∧ TwistedD4Frame G f)

end CFSG.Timmesfeld.ARS
