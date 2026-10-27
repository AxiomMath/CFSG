module

public import CFSG.Milestones.ASVolI.F48.Sp4
public import CFSG.Milestones.ASVolI.F48.Un
public import CFSG.Milestones.ASVolI.F48.D4
public import CFSG.Milestones.ASVolI.F48.Native

public section

namespace CFSG.ASVolI

open CFSG.Open

section

theorem burnsideF48_concl_L3_native (hF : F_4_5) {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 .L3 p f Gp M₁ M₂) (hq : 3 ≤ p ^ f) :
    ChF.F48Concl .L3 p f Gp M₁ M₂ :=
  burnsideF48_concl_L3 hF ChF.nativeChartCompatibility hyp hq

theorem burnsideF48_concl_Sp4_native (hF : F_4_5) {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 .Sp4 p f Gp M₁ M₂) (hq : 4 ≤ p ^ f) :
    ChF.F48Concl .Sp4 p f Gp M₁ M₂ :=
  burnsideF48_concl_Sp4 hF ChF.nativeChartCompatibility hyp hq

theorem burnsideF48_concl_U4_native (hF : F_4_5) {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 .U4 p f Gp M₁ M₂) (hq : 3 ≤ p ^ f) :
    ChF.F48Concl .U4 p f Gp M₁ M₂ :=
  burnsideF48_concl_U4 hF ChF.nativeChartCompatibility hyp hq

theorem burnsideF48_concl_U5_native (hF : F_4_5) {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 .U5 p f Gp M₁ M₂) (hq : 3 ≤ p ^ f) :
    ChF.F48Concl .U5 p f Gp M₁ M₂ :=
  burnsideF48_concl_U5 hF ChF.nativeChartCompatibility hyp hq

theorem burnsideF48_concl_G2_native (hF : F_4_5) {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 .G2 p f Gp M₁ M₂) (hq : 4 ≤ p ^ f) :
    ChF.F48Concl .G2 p f Gp M₁ M₂ :=
  burnsideF48_concl_G2 hF ChF.nativeChartCompatibility hyp hq

end

section

theorem burnsideF48_concl_D4tw_native (hF : F_4_5) {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 .D4tw p f Gp M₁ M₂) (hq : 4 ≤ p ^ f) :
    ChF.F48Concl .D4tw p f Gp M₁ M₂ :=
  burnsideF48_concl_D4tw hF ChF.nativeChartCompatibility hyp hq

@[expose] def burnsideF48_Small : Prop :=
  ∀ (κ : ChF.GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    ChF.HypF_4_4 κ p f Gp M₁ M₂ → p ^ f ≤ 3 → ¬ ((κ = .L3 ∨ κ = .U4 ∨ κ = .U5) ∧ p ^ f = 3) →
      ChF.F48Concl κ p f Gp M₁ M₂

theorem burnsideF48_of_small (hF : F_4_5) (hs : burnsideF48_Small) : F_4_8 := by
  intro κ p f E _ Gp M₁ M₂ hyp
  by_cases hsm : p ^ f ≤ 3 ∧ ¬ ((κ = .L3 ∨ κ = .U4 ∨ κ = .U5) ∧ p ^ f = 3)
  · exact hs κ p f E Gp M₁ M₂ hyp hsm.1 hsm.2
  · by_cases hq : 4 ≤ p ^ f
    · by_cases h2 : p = 2
      · subst h2
        have hf : 2 ≤ f := by
          rcases Nat.lt_or_ge f 2 with h | h
          · interval_cases f <;> norm_num at hq
          · exact h
        exact burnsideF48_concl_two_ge4_native hf hyp
      · have hκ : κ = .L3 ∨ κ = .Sp4 ∨ κ = .G2 ∨ κ = .D4tw ∨ κ = .U4 ∨ κ = .U5 := by
          cases κ
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact absurd hyp.model.1 h2
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
          · exact absurd hyp.model.1 h2
          · exact absurd hyp.model.1 h2
        rcases hκ with rfl | rfl | rfl | rfl | rfl | rfl
        · exact burnsideF48_concl_L3_native hF hyp (by omega)
        · exact burnsideF48_concl_Sp4_native hF hyp hq
        · exact burnsideF48_concl_G2_native hF hyp hq
        · exact burnsideF48_concl_D4tw_native hF hyp hq
        · exact burnsideF48_concl_U4_native hF hyp (by omega)
        · exact burnsideF48_concl_U5_native hF hyp (by omega)
    · have hl3 : (κ = .L3 ∨ κ = .U4 ∨ κ = .U5) ∧ p ^ f = 3 := by
        by_contra hc
        exact hsm ⟨by omega, hc⟩
      obtain ⟨hκ, h3⟩ := hl3
      rcases hκ with rfl | rfl | rfl
      · exact burnsideF48_concl_L3_native hF hyp (by omega)
      · exact burnsideF48_concl_U4_native hF hyp (by omega)
      · exact burnsideF48_concl_U5_native hF hyp (by omega)

end

end CFSG.ASVolI
