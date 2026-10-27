module

public import CFSG.Milestones.ASVolI.F429.Cl7
public import CFSG.Milestones.ASVolI.F429.Cl38
public import CFSG.Milestones.ASVolI.F429.C8Small

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

@[expose] def burnsideF429_C8Small' : Prop :=
  ∀ (κ : GLKind) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E), HypF_4_4 κ 2 1 Gp M₁ M₂ →
    (κ = .Sp4 ∨ κ = .G2 ∨ κ = .F4tw) → burnsideF429_C8 κ 1 Gp M₁ M₂

theorem burnsideF429_C8Small_of (h : burnsideF429_C8Small') : burnsideF429_C8Small := by
  intro κ E _ Gp M₁ M₂ hyp hκ
  rcases hκ with rfl | hκ
  · exact burnsideF429_c8_L3two hyp
  · exact h _ E Gp M₁ M₂ hyp hκ

@[expose] def burnsideF429_C7ZInput' : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ 2 f Gp M₁ M₂ → (κ = .L3 ∨ κ = .Sp4) → 2 ≤ f →
    ∀ T : Subgroup E, ChF.IsSylowOf 2 T (M₁ ⊓ M₂) → ctr T ≤ Gp

@[expose] def burnsideF429_KeyInput : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ 2 f Gp M₁ M₂ → κ.IsLie → ¬ burnsideF429_OddCase κ f →
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ Gp ⊓ (M₁ ⊓ M₂), r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp

section Main

theorem burnsideF429_C7ZInput_of (h : burnsideF429_C7ZInput') : burnsideF429_C7ZInput := by
  intro κ f E _ Gp M₁ M₂ hyp hκ T hT
  haveI := hyp.finite
  haveI := hyp.normal
  by_cases hf : 2 ≤ f
  · exact h κ f E Gp M₁ M₂ hyp hκ hf T hT
  · have hf1 : f = 1 := by
      have : 1 ≤ f := by rcases hκ with rfl | rfl <;> exact hyp.model.2.1
      omega
    subst hf1
    have hL : κ.IsLie := by rcases hκ with rfl | rfl <;> exact ⟨by decide, by decide⟩
    have hU : κ ≠ .U4 ∧ κ ≠ .U5 := by rcases hκ with rfl | rfl <;> exact ⟨by decide, by decide⟩
    exact inf_le_left.trans (burnsideF429_le_of_odd (burnsideF429_odd_index_two hyp hL hU) hT.2.1)

theorem burnsideF429_clause4_of (hkey : burnsideF429_KeyInput) :
    ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 κ 2 f Gp M₁ M₂ → κ.IsLie → burnsideF429_C4 Gp M₁ M₂ := by
  intro κ f E _ Gp M₁ M₂ hyp hκ
  by_cases hc : burnsideF429_OddCase κ f
  · exact burnsideF429_C4_of_odd hyp (burnsideF429_odd_index_of_case hyp hκ hc)
  · exact burnsideF429_C4_of_key hyp (hkey κ f E Gp M₁ M₂ hyp hκ hc)

end Main

end CFSG.ASVolI
