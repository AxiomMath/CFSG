module

public import CFSG.Milestones.ASVolI.F431.BCoreG2
public import CFSG.Milestones.ASVolI.F431.BCoreD4
public import CFSG.Milestones.ASVolI.F431.BCoreU4Q
public import CFSG.Milestones.ASVolI.F431.BCoreU5
public import CFSG.Milestones.ASVolI.F431.BCoreSpAll

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Open

theorem burnsideF4m_lieCoreInput_U :
    ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 κ 2 f Gp M₁ M₂ → 2 ≤ f → (κ = .U4 ∨ κ = .U5) → ¬ Odd Gp.index →
      burnsideF4m_Core1 Gp M₁ ∧ burnsideF4m_Core2 κ Gp M₂ ∧
        pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂) := by
  intro κ f E _ Gp M₁ M₂ hyp hf hκ _
  haveI := hyp.finite
  rcases hκ with rfl | rfl
  · exact ⟨(burnsideF4m_core12_U4 hyp hf).1, (burnsideF4m_core12_U4 hyp hf).2,
      burnsideF4m_U4_pCore hyp hf⟩
  · exact ⟨(burnsideF4m_core12_U5 hyp hf).1, (burnsideF4m_core12_U5 hyp hf).2,
      burnsideF4m_U5_pCore hyp hf⟩

theorem burnsideF4m_lieCoreInput_Sp4 :
    ∀ (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 .Sp4 2 f Gp M₁ M₂ → 2 ≤ f → ¬ Odd Gp.index →
      burnsideF4m_Core1 Gp M₁ ∧ burnsideF4m_Core2 .Sp4 Gp M₂ ∧
        pCoreOf 2 M₁ = pCoreOf 2 (Gp ⊓ M₁) ∧ pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂) ∧
        pCoreOf 2 (M₁ ⊓ M₂) = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) :=
  fun f E _ Gp M₁ M₂ hyp hf _ => burnsideF4m_lieCoreSp f E Gp M₁ M₂ hyp hf

section Top

set_option linter.unusedSectionVars false


theorem burnsideF4m_lieCoreInput_G2D4 :
    ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 κ 2 f Gp M₁ M₂ → 2 ≤ f → (κ = .G2 ∨ κ = .D4tw) → ¬ Odd Gp.index →
      burnsideF4m_Core1 Gp M₁ ∧ burnsideF4m_Core2 κ Gp M₂ := by
  intro κ f E _ Gp M₁ M₂ hyp hf hκ _
  rcases hκ with rfl | rfl
  · exact burnsideF4m_core12_G2 hyp hf
  · exact burnsideF4m_core12_D4 hyp hf

theorem burnsideF4m_lieCoreInput : burnsideF4m_LieCoreInput :=
  ⟨burnsideF4m_lieCoreInput_G2D4, burnsideF4m_lieCoreInput_U, burnsideF4m_lieCoreInput_Sp4⟩

end Top

end CFSG.ASVolI
