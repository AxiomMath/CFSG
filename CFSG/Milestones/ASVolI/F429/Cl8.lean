module

public import CFSG.Milestones.ASVolI.F429.Main
public import CFSG.Milestones.ASVolI.F429.Sp2
public import CFSG.Milestones.ASVolI.F429.bC8F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Clause8


theorem burnsideF429_c8_G2two {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2 2 1 Gp M₁ M₂) : burnsideF429_C8 .G2 1 Gp M₁ M₂ := by
  obtain ⟨ha, hb⟩ := burnsideF429b_c8sbar_G2two hyp
  exact burnsideF429_c8_of (κ := .G2) (f := 1) ha (Or.inr ⟨rfl, Or.inr (Or.inl rfl), hb⟩)

theorem burnsideF429_c8Small'_of
    (hF4 : ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E), HypF_4_4 .F4tw 2 1 Gp M₁ M₂ →
      burnsideF429_C8 .F4tw 1 Gp M₁ M₂) : burnsideF429_C8Small' := by
  intro κ E _ Gp M₁ M₂ hyp hκ
  rcases hκ with rfl | rfl | rfl
  · exact burnsideF429_c8_Sp4two hyp
  · exact burnsideF429_c8_G2two hyp
  · exact hF4 E Gp M₁ M₂ hyp

end Clause8

section Clause8All


theorem burnsideF429_c8_F4two {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .F4tw 2 1 Gp M₁ M₂) : burnsideF429_C8 .F4tw 1 Gp M₁ M₂ := by
  obtain ⟨ha, hb⟩ := burnsideF429b_c8sbar_F4two hyp
  exact burnsideF429_c8_of (κ := .F4tw) (f := 1) ha (Or.inr ⟨rfl, Or.inr (Or.inr rfl), hb⟩)

theorem burnsideF429_clause8 :
    ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 κ 2 f Gp M₁ M₂ → κ.IsLie → burnsideF429_C8 κ f Gp M₁ M₂ :=
  burnsideF429_clause8_of (burnsideF429_C8Small_of (burnsideF429_c8Small'_of
    fun E _ _ _ _ hyp => burnsideF429_c8_F4two hyp))

end Clause8All

end CFSG.ASVolI
