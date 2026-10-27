module

public import CFSG.Milestones.ASVolI.F48.Core

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

theorem burnsideF48s_isLieExtGroup_E (hcompat : NativeChartCompatibilityGoal) {κ : GLKind}
    {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) :
    IsLieExtGroup E κ p f :=
  ⟨Gp, hyp.model, hyp.normal, hyp.centralizer_trivial, Gp ⊓ (M₁ ⊓ M₂), Gp ⊓ M₁, Gp ⊓ M₂,
    burnsideF48_parabolics_of_compat hcompat hyp, hyp.dynkin⟩

theorem burnsideF48s_concl_of_qe {κ : GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hext : IsLieExtGroup E κ p f) {Y₀ : Type} [Group Y₀]
    (β₀ : Cpl M₁ M₂ Y₀) (hβ₀ : β₀.IsFaithful) (hs₀ : β₀.IsSmall κ.m) (eY₀ : Y₀ ≃* E)
    (hqe : ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
      Amalgam.Completion.IsQuasiEquivalent β.toCompletion β₀.toCompletion) :
    F48Concl κ p f Gp M₁ M₂ := by
  have hiso : ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
      Nonempty (β.G0 ≃* E) := by
    intro Y _ β hβ hs
    obtain ⟨φ, -, -⟩ := hqe Y β hβ hs
    exact ⟨(burnsideF48_G0Equiv β).trans (φ.trans eY₀)⟩
  refine ⟨fun Y _ β hβ hs => ?_, fun _ => ⟨⟨Y₀, inferInstance, β₀, hβ₀, hs₀, hqe⟩, hiso⟩⟩
  obtain ⟨e⟩ := hiso Y β hβ hs
  exact ⟨Y, inferInstance, β, Amalgam.Completion.IsEquivalent.refl _,
    burnsideF48_isLieExtGroup_of_equiv e.symm hext, ⟨MulEquiv.refl _⟩⟩

end CFSG.ASVolI
