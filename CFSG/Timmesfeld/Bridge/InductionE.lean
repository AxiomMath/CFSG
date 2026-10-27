module

public import CFSG.Timmesfeld.Bridge.RootSetsThird
public import CFSG.Timmesfeld.Bridge.RootSets
public import CFSG.Timmesfeld.Bridge.RootSetsFrame

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

@[expose] def RootIHStructE (G : Type) [Group G] : Prop :=
  ∀ (G' : Type) [Group G'] (D' : Set G'), Hyp G' D' → Nat.card G' < Nat.card G →
    Outcome G' ∧ ((∃ d ∈ D', ∃ e ∈ rootSet D' d, e ≠ d) →
      RootClosure D' ∧ SpecialClosure D' ∧ RootMoufang D' ∧ ExistsCommSpec D')

theorem RootIHStructE.toStruct {G : Type} [Group G] (h : RootIHStructE G) : RootIHStruct G :=
  fun G' _ D' h' hlt => ⟨(h G' D' h' hlt).1, fun hl =>
    let ⟨hc, hs, hm, _⟩ := (h G' D' h' hlt).2 hl
    ⟨hc, hs, hm⟩⟩

@[expose] def ExistsCommSpecStepE : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIHStructE G →
    (∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) → RootClosure D → SpecialClosure D → ExistsCommSpec D

@[expose] def LargeStepSE : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIHStructE G →
    (∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) →
      RootClosure D ∧ SpecialClosure D ∧ RootMoufang D ∧ ExistsCommSpec D

theorem largeStepSE_of_third (h1 : ThirdKindStep) (h2 : GammaResidualStep) (h3 : CommLambdaStep)
    (h4 : ExistsCommSpecStepE) : LargeStepSE := by
  intro G _ D hH IH hl
  have hc := rootClosure_of_rootFixThird hH (h1 G D hH IH.toStruct hl)
  have hs := gammaStep_of_residual h2 G D hH IH.toStruct.rootIH hl hc
  have he := h4 G D hH IH hl hc hs
  exact ⟨hc, hs, rootMoufang_of_frameInput hH hc hs
    (frameInput_of_commLambda hH hs (h3 G D hH IH.toStruct.rootIH hl hc hs) he), he⟩

end CFSG.Timmesfeld.Bridge
