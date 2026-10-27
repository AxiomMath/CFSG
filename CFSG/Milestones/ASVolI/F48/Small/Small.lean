module

public import CFSG.Milestones.ASVolI.F48.Small.L3
public import CFSG.Milestones.ASVolI.F48.Small.Sp42
public import CFSG.Milestones.ASVolI.F48.Small.Tits
public import CFSG.Milestones.ASVolI.F48.Small.TwoF4
public import CFSG.Milestones.ASVolI.F48.Small.G22
public import CFSG.Milestones.ASVolI.F48.Small.D42
public import CFSG.Milestones.ASVolI.F48.Small.U42e
public import CFSG.Milestones.ASVolI.F48.Small.Sp43
public import CFSG.Milestones.ASVolI.F48.Small.Sp43e
public import CFSG.Milestones.ASVolI.F48.Odd

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF

@[expose] def burnsideF48s_SmallRest : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ →
    ((κ = .G2 ∨ κ = .D4tw) ∧ p = 3 ∧ f = 1) ∨ (κ = .U5 ∧ p = 2 ∧ f = 1) →
    F48Concl κ p f Gp M₁ M₂

theorem burnsideF48s_small_q {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hq : p ^ f ≤ 3) :
    (p = 2 ∧ f = 1) ∨ (p = 3 ∧ f = 1) := by
  have h2 := hp.two_le
  have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  have hf1 : f = 1 := by
    by_contra hne
    have h4 : p ^ 2 ≤ p ^ f := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  subst hf1
  rw [pow_one] at hq
  omega


theorem burnsideF48s_small_of_rest (h45 : F_4_5) (h46 : F_4_6) (hrest : burnsideF48s_SmallRest) :
    burnsideF48_Small := by
  intro κ p f E _ Gp M₁ M₂ hyp hq hnot
  cases κ with
  | L3 =>
    obtain ⟨hp, hf, -⟩ := hyp.model
    rcases burnsideF48s_small_q hp hf hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact burnsideF48s_small_L3_two hyp
    · exact absurd ⟨Or.inl rfl, by norm_num⟩ hnot
  | Sp4 =>
    obtain ⟨hp, hf, -⟩ := hyp.model
    rcases burnsideF48s_small_q hp hf hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact burnsideF48s_small_Sp4_two h45 h46 hyp
    · by_cases hGp : Gp = ⊤
      · exact burnsideF48s_small_Sp4_three_top h45 h46 hyp hGp
      · exact burnsideF48s_small_Sp4_three_ext h45 h46 hyp hGp
  | G2 =>
    obtain ⟨hp, hf, -⟩ := hyp.model
    rcases burnsideF48s_small_q hp hf hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact burnsideF48s_small_G2_two h45 h46 hyp
    · exact hrest _ _ _ E Gp M₁ M₂ hyp (Or.inl ⟨Or.inl rfl, rfl, rfl⟩)
  | D4tw =>
    obtain ⟨hp, hf, -⟩ := hyp.model
    rcases burnsideF48s_small_q hp hf hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact burnsideF48s_d42_small h45 h46 hyp
    · exact hrest _ _ _ E Gp M₁ M₂ hyp (Or.inl ⟨Or.inr rfl, rfl, rfl⟩)
  | F4tw => exact burnsideF48s_small_F4tw_two h45 h46 hyp hq
  | U4 =>
    obtain ⟨hp, hf, -⟩ := hyp.model
    rcases burnsideF48s_small_q hp hf hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · by_cases hGp : Gp = ⊤
      · exact burnsideF48s_small_U4_two_top h45 h46 hyp hGp
      · exact burnsideF48s_small_U4_two_ext h45 h46 hyp hGp
    · exact absurd ⟨Or.inr (Or.inl rfl), by norm_num⟩ hnot
  | U5 =>
    obtain ⟨hp, hf, -⟩ := hyp.model
    rcases burnsideF48s_small_q hp hf hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hrest _ _ _ E Gp M₁ M₂ hyp (Or.inr ⟨rfl, rfl, rfl⟩)
    · exact absurd ⟨Or.inr (Or.inr rfl), by norm_num⟩ hnot
  | G2d => exact burnsideF48s_small_G2d h45 h46 hyp
  | Tits => exact burnsideF48s_small_Tits h45 h46 hyp

theorem burnsideF48s_F_4_8_of_rest (h45 : F_4_5) (h46 : F_4_6) (hrest : burnsideF48s_SmallRest) :
    F_4_8 :=
  burnsideF48_of_small h45 (burnsideF48s_small_of_rest h45 h46 hrest)

end CFSG.ASVolI
