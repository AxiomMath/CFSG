module

public import CFSG.Milestones.ASVolI.F429.Main
public import CFSG.Milestones.ASVolI.F429.C7Shape
public import CFSG.Milestones.ASVolI.F429.aC4L3
public import CFSG.Milestones.ASVolI.F429.aC4U
public import CFSG.Milestones.ASVolI.F429.aC4Sp4
public import CFSG.Milestones.ASVolI.F429.aC4CtrL3
public import CFSG.Milestones.ASVolI.F429.aC4CtrSp4
public import CFSG.Milestones.ASVolI.F429.bC4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

theorem burnsideF429_one_le_f {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hκ : κ.IsLie) : 1 ≤ f := by
  cases κ <;> first
    | exact hyp.model.2.1
    | exact absurd rfl hκ.1
    | exact absurd rfl hκ.2
    | (obtain ⟨-, hodd, -⟩ := hyp.model; exact hodd.pos)

theorem burnsideF429_c7ZInput' : burnsideF429_C7ZInput' := by
  intro κ f E _ Gp M₁ M₂ hyp hκ hf T hT
  rcases hκ with rfl | rfl
  · exact burnsideF429a_ctr_L3 hyp hf hT
  · exact burnsideF429a_ctr_Sp4 hyp hf hT

section Clauses


theorem burnsideF429_keyInput : burnsideF429_KeyInput := by
  intro κ f E _ Gp M₁ M₂ hyp hκ hc
  have hf1 := burnsideF429_one_le_f hyp hκ
  have hnot1 : (κ ≠ .U4 ∧ κ ≠ .U5) → 2 ≤ f := fun hU => by
    by_contra h
    exact hc (Or.inr (Or.inr ⟨by omega, hU⟩))
  cases κ with
  | L3 => exact burnsideF429a_key_L3 hyp (hnot1 ⟨by decide, by decide⟩)
  | Sp4 => exact burnsideF429a_key_Sp4 hyp (hnot1 ⟨by decide, by decide⟩)
  | G2 => exact burnsideF429b_key4_G2 hyp (hnot1 ⟨by decide, by decide⟩)
  | D4tw => exact burnsideF429b_key4_D4tw hyp
  | F4tw => exact absurd (Or.inl rfl) hc
  | U4 => exact burnsideF429a_key_U4 hyp
  | U5 => exact burnsideF429a_key_U5 hyp
  | G2d => exact absurd rfl hκ.1
  | Tits => exact absurd rfl hκ.2

theorem burnsideF429_clause4 :
    ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 κ 2 f Gp M₁ M₂ → κ.IsLie → burnsideF429_C4 Gp M₁ M₂ :=
  burnsideF429_clause4_of burnsideF429_keyInput

theorem burnsideF429_clause7 :
    ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      ∀ hyp : HypF_4_4 κ 2 f Gp M₁ M₂, κ.IsLie →
      ∀ T : Subgroup E, ChF.IsSylowOf 2 T (M₁ ⊓ M₂) → burnsideF429_C7 κ Gp M₁ M₂ hyp T :=
  burnsideF429_clause7_of (burnsideF429_C7ZInput_of burnsideF429_c7ZInput')
    burnsideF429_c7ClassicalShape

end Clauses

end CFSG.ASVolI
