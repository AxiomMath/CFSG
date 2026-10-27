module

public import CFSG.Timmesfeld.Bridge.Gamma
public import CFSG.Timmesfeld.RootInduction

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

@[expose] def GammaStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIH G →
    (∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) → RootClosure D → SpecialClosure D

@[expose] def GammaResidualStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIH G →
    (∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) → RootClosure D → GammaMixed D ∧ GammaDouble D

theorem gammaStep_of_residual (h : GammaResidualStep) : GammaStep := by
  intro G _ D hH IH hl hc
  have := hH.finite
  obtain ⟨hM, hS⟩ := h G D hH IH hl hc
  exact specialClosure_of_residual hH.isClass hH.root hM hS

end CFSG.Timmesfeld.Bridge
