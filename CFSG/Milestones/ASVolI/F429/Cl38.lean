module

public import CFSG.Milestones.ASVolI.F429.aC8
public import CFSG.Milestones.ASVolI.F429.aC8U5
public import CFSG.Milestones.ASVolI.F429.bC3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Milestones.ASVolI.F429.C8
public import CFSG.Milestones.ASVolI.F429.Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Clauses


theorem burnsideF429_sbar_le_perfectCore {κ : GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hκ : κ.IsLie) (hf : 2 ≤ f) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∧
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂) := by
  cases κ with
  | L3 => exact burnsideF429a_c3_sbar_classical (Or.inl rfl) hyp hf
  | Sp4 => exact burnsideF429a_c3_sbar_classical (Or.inr (Or.inl rfl)) hyp hf
  | U4 => exact burnsideF429a_c3_sbar_classical (Or.inr (Or.inr (Or.inl rfl))) hyp hf
  | U5 => exact burnsideF429a_c3_sbar_classical (Or.inr (Or.inr (Or.inr rfl))) hyp hf
  | G2 => exact burnsideF429b_c3_G2 hyp hf
  | D4tw => exact burnsideF429b_c3_D4tw hyp hf
  | F4tw => exact burnsideF429b_c3_F4tw hyp hf
  | G2d => exact absurd rfl hκ.1
  | Tits => exact absurd rfl hκ.2

theorem burnsideF429_clause3 :
    ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 κ 2 f Gp M₁ M₂ → κ.IsLie → burnsideF429_C3 f Gp M₁ M₂ := by
  intro κ f E _ Gp M₁ M₂ hyp hκ hf
  obtain ⟨h1, h2⟩ := burnsideF429_sbar_le_perfectCore hyp hκ hf
  exact burnsideF429_clause3_of hyp h1 h2

@[expose] def burnsideF429_C8Small : Prop :=
  ∀ (κ : GLKind) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E), HypF_4_4 κ 2 1 Gp M₁ M₂ →
    (κ = .L3 ∨ κ = .Sp4 ∨ κ = .G2 ∨ κ = .F4tw) → burnsideF429_C8 κ 1 Gp M₁ M₂

theorem burnsideF429_clause8_of (hsmall : burnsideF429_C8Small) :
    ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 κ 2 f Gp M₁ M₂ → κ.IsLie → burnsideF429_C8 κ f Gp M₁ M₂ := by
  intro κ f E _ Gp M₁ M₂ hyp hκ
  haveI := hyp.finite
  by_cases hf : 2 ≤ f
  · exact burnsideF429_c8_of_le_perfectCore (Or.inl (burnsideF429_sbar_le_perfectCore hyp hκ hf).1)
  · have hf1 : f = 1 := by
      have : 1 ≤ f := by
        cases κ <;> first
          | exact hyp.model.2.1
          | exact absurd rfl hκ.1
          | exact absurd rfl hκ.2
          | (obtain ⟨-, hodd, -⟩ := hyp.model; exact hodd.pos)
      omega
    subst hf1
    cases κ with
    | L3 => exact hsmall _ E Gp M₁ M₂ hyp (Or.inl rfl)
    | Sp4 => exact hsmall _ E Gp M₁ M₂ hyp (Or.inr (Or.inl rfl))
    | G2 => exact hsmall _ E Gp M₁ M₂ hyp (Or.inr (Or.inr (Or.inl rfl)))
    | F4tw => exact hsmall _ E Gp M₁ M₂ hyp (Or.inr (Or.inr (Or.inr rfl)))
    | D4tw => exact burnsideF429_c8_of_le_perfectCore (burnsideF429b_c8_D4tw hyp)
    | U4 => exact burnsideF429_c8_of_le_perfectCore (burnsideF429a_c8_U4two hyp)
    | U5 => exact burnsideF429_c8_of_le_perfectCore (burnsideF429a_c8_U5two hyp)
    | G2d => exact absurd rfl hκ.1
    | Tits => exact absurd rfl hκ.2

end Clauses

end CFSG.ASVolI
