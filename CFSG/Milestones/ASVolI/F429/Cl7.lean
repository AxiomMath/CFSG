module

public import CFSG.Milestones.ASVolI.F429.Ctr
public import CFSG.Milestones.ASVolI.F429.OutOdd
public import CFSG.Milestones.ASVolI.F429.bC7F4
public import CFSG.Milestones.ASVolI.F429.Gen
public import CFSG.Milestones.ASVolI.F429.One

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Odd

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_odd_index_F4tw (hyp : HypF_4_4 .F4tw 2 f Gp M₁ M₂) : Odd Gp.index := by
  haveI := hyp.finite
  haveI := hyp.normal
  by_cases hf : 2 ≤ f
  · refine burnsideF429_odd_index_of_outer hyp.centralizer_trivial ?_
    rw [burnsideF429_card_outer_F4tw hyp hf]
    exact hyp.model.2.1
  · have hf1 : f = 1 := by
      have := hyp.model.2.1.pos
      omega
    subst hf1
    rw [burnsideF429_top_F4two hyp, Subgroup.index_top]
    exact odd_one

theorem burnsideF429_odd_index_G2 (hyp : HypF_4_4 .G2 2 f Gp M₁ M₂) (hfo : Odd f) :
    Odd Gp.index := by
  haveI := hyp.finite
  haveI := hyp.normal
  by_cases hf : 2 ≤ f
  · refine burnsideF429_odd_index_of_outer hyp.centralizer_trivial ?_
    rw [burnsideF429_card_outer_G2 hyp hf]
    exact hfo
  · have hf1 : f = 1 := by
      have := hfo.pos
      omega
    subst hf1
    rw [burnsideF429_top_G2two hyp, Subgroup.index_top]
    exact odd_one

theorem burnsideF429_odd_index_D4tw (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂) (hfo : Odd f) :
    Odd Gp.index := by
  haveI := hyp.finite
  haveI := hyp.normal
  refine burnsideF429_odd_index_of_outer hyp.centralizer_trivial ?_
  rw [burnsideF429_card_outer_D4tw hyp]
  exact Odd.mul (by decide) hfo

theorem burnsideF429_odd_index_two {κ : GLKind} (hyp : HypF_4_4 κ 2 1 Gp M₁ M₂) (hκ : κ.IsLie)
    (hU : κ ≠ .U4 ∧ κ ≠ .U5) : Odd Gp.index := by
  rcases burnsideF429_clause1 κ 1 E Gp M₁ M₂ hyp hκ rfl with h | ⟨-, h, -⟩ | ⟨h, -⟩
  · rw [h, Subgroup.index_top]
    exact odd_one
  · rw [h]
    decide
  · rcases h with rfl | rfl
    · exact absurd rfl hU.1
    · exact absurd rfl hU.2

end Odd

@[expose] def burnsideF429_C7ZInput : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ 2 f Gp M₁ M₂ → (κ = .L3 ∨ κ = .Sp4) →
    ∀ T : Subgroup E, ChF.IsSylowOf 2 T (M₁ ⊓ M₂) → ctr T ≤ Gp

@[expose] def burnsideF429_C7ClassicalShape : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E)
    (hyp : HypF_4_4 κ 2 f Gp M₁ M₂), (κ = .L3 ∨ κ = .Sp4 ∨ κ = .U4 ∨ κ = .U5) →
    (ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) = ctr (oPPrime 2 (Gp ⊓ M₁)) ∨
      (κ = .L3 ∧ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) = hyp.toHypF_4_4g.chart.longRoot) ∨
      (κ = .Sp4 ∧ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) =
        ctr (oPPrime 2 (Gp ⊓ M₁)) ⊔ ctr (oPPrime 2 (Gp ⊓ M₂)) ∧
        ctr (oPPrime 2 (Gp ⊓ M₁)) ⊓ ctr (oPPrime 2 (Gp ⊓ M₂)) = ⊥ ∧
        ctr (oPPrime 2 (Gp ⊓ M₁)) = hyp.toHypF_4_4g.chart.longRoot ∧
        ctr (oPPrime 2 (Gp ⊓ M₂)) = hyp.toHypF_4_4g.chart.shortRoot))

section Clause

theorem burnsideF429_ctr_le_of (hZ : burnsideF429_C7ZInput) {κ : GLKind} {f : ℕ} {E : Type}
    [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hκ : κ.IsLie)
    {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : ctr T ≤ Gp := by
  haveI := hyp.finite
  haveI := hyp.normal
  cases κ with
  | L3 => exact hZ _ f E Gp M₁ M₂ hyp (Or.inl rfl) T hT
  | Sp4 => exact hZ _ f E Gp M₁ M₂ hyp (Or.inr rfl) T hT
  | G2 =>
    by_cases hf : 2 ≤ f
    · exact fun x hx => burnsideF429_m_ctr_le_G2 hyp hf hT hx
    · have hf1 : f = 1 := by
        have := hyp.model.2.1
        omega
      subst hf1
      exact inf_le_left.trans (burnsideF429_le_of_odd (burnsideF429_odd_index_G2 hyp odd_one)
        hT.2.1)
  | D4tw => exact fun x hx => burnsideF429_m_ctr_le_D4tw hyp hT hx
  | F4tw => exact inf_le_left.trans (burnsideF429_le_of_odd (burnsideF429_odd_index_F4tw hyp) hT.2.1)
  | U4 => exact fun x hx => burnsideF429_m_ctr_le_U4_all hyp hT hx
  | U5 => exact fun x hx => burnsideF429_m_ctr_le_U5_all hyp hT hx
  | G2d => exact absurd rfl hκ.1
  | Tits => exact absurd rfl hκ.2

theorem burnsideF429_clause7_of (hZ : burnsideF429_C7ZInput)
    (hshape : burnsideF429_C7ClassicalShape) :
    ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      ∀ hyp : HypF_4_4 κ 2 f Gp M₁ M₂, κ.IsLie →
      ∀ T : Subgroup E, ChF.IsSylowOf 2 T (M₁ ⊓ M₂) → burnsideF429_C7 κ Gp M₁ M₂ hyp T := by
  intro κ f E _ Gp M₁ M₂ hyp hκ T hT
  refine ⟨burnsideF429_ctr_of_le hyp hT (burnsideF429_ctr_le_of hZ hyp hκ hT), ?_⟩
  cases κ with
  | L3 => exact hshape _ f E Gp M₁ M₂ hyp (Or.inl rfl)
  | Sp4 => exact hshape _ f E Gp M₁ M₂ hyp (Or.inr (Or.inl rfl))
  | U4 => exact hshape _ f E Gp M₁ M₂ hyp (Or.inr (Or.inr (Or.inl rfl)))
  | U5 => exact hshape _ f E Gp M₁ M₂ hyp (Or.inr (Or.inr (Or.inr rfl)))
  | G2 => exact Or.inl (burnsideF429b_c7_G2 hyp)
  | D4tw => exact Or.inl (burnsideF429b_c7_D4tw hyp)
  | F4tw => exact Or.inl (burnsideF429b_c7_F4tw hyp)
  | G2d => exact absurd rfl hκ.1
  | Tits => exact absurd rfl hκ.2

end Clause

end CFSG.ASVolI

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section OddCases

@[expose] def burnsideF429_OddCase (κ : GLKind) (f : ℕ) : Prop :=
  κ = .F4tw ∨ ((κ = .G2 ∨ κ = .D4tw) ∧ Odd f) ∨ (f = 1 ∧ κ ≠ .U4 ∧ κ ≠ .U5)

variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_odd_index_of_case (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hκ : κ.IsLie)
    (hc : burnsideF429_OddCase κ f) : Odd Gp.index := by
  rcases hc with rfl | ⟨rfl | rfl, hfo⟩ | ⟨rfl, hU⟩
  · exact burnsideF429_odd_index_F4tw hyp
  · exact burnsideF429_odd_index_G2 hyp hfo
  · exact burnsideF429_odd_index_D4tw hyp hfo
  · exact burnsideF429_odd_index_two hyp hκ hU

end OddCases

end CFSG.ASVolI
