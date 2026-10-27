module

public import CFSG.Milestones.ASVolI.F431.Ctr
public import CFSG.Milestones.ASVolI.F431.ATop
public import CFSG.Milestones.ASVolI.F431.A

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section F433Un

set_option linter.unusedSectionVars false


@[expose] def burnsideF4m_CtrInputUn : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E), HypF_4_4 κ 2 f Gp M₁ M₂ →
    ((κ = .U4 ∧ f = 1) ∨ (κ = .U5 ∧ f ≠ 2)) →
    ∀ T : Subgroup E, IsSylowTwoOf T (M₁ ⊓ M₂) → ∀ x ∈ ctr T, x * x = 1 → x ∈ Gp

theorem burnsideF4m_ctrInputRest_of_un (hin : burnsideF4m_CtrInputUn) :
    burnsideF4m_CtrInputRest := by
  intro κ f E _ Gp M₁ M₂ hyp hκ T hT x hx hx2
  rcases hκ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hf⟩ | ⟨rfl, rfl⟩
  · rw [burnsideF4m_top_G2two hyp]; exact Subgroup.mem_top x
  · exact hin _ 1 E Gp M₁ M₂ hyp (Or.inl ⟨rfl, rfl⟩) T hT x hx hx2
  · exact hin _ f E Gp M₁ M₂ hyp (Or.inr ⟨rfl, hf⟩) T hT x hx hx2
  · rw [burnsideF4m_top_F4two hyp]; exact Subgroup.mem_top x

theorem burnsideF4m_F_4_33_of_un (hin : burnsideF4m_CtrInputUn) : F_4_33 :=
  burnsideF4m_F_4_33_of (burnsideF4m_ctrInputRest_of_un hin)

@[expose] def burnsideF4m_OddIndexInputRest : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M →
    ((κ = .Sp4 ∧ (Even f ∨ f = 1)) ∨ (κ = .G2 ∧ Even f) ∨ (κ = .D4tw ∧ Even f) ∨
      κ = .U4 ∨ κ = .U5) → Odd Gp.index

theorem burnsideF4m_oddIndexInputRest_j (hodd : burnsideF4m_OddIndexInputRest) :
    burnsideF4j_OddIndexInputRest := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL43 hκ
  have hindex_one : Gp = ⊤ → Odd Gp.index := fun h => by
    rw [h, Subgroup.index_top]; exact odd_one
  rcases hκ with ⟨rfl, hf⟩ | ⟨rfl, hf | rfl⟩ | ⟨rfl, hf⟩ | ⟨rfl, rfl⟩ | rfl | rfl
  · exact hodd _ f E Gp M₁ M₂ Y β M ε z hyp hL43 (Or.inl ⟨rfl, hf⟩)
  · exact hodd _ f E Gp M₁ M₂ Y β M ε z hyp hL43 (Or.inr (Or.inl ⟨rfl, hf⟩))
  · exact hindex_one (burnsideF4m_top_G2two hyp.amalgam)
  · exact hodd _ f E Gp M₁ M₂ Y β M ε z hyp hL43 (Or.inr (Or.inr (Or.inl ⟨rfl, hf⟩)))
  · exact hindex_one (burnsideF4m_top_F4two hyp.amalgam)
  · exact hodd _ f E Gp M₁ M₂ Y β M ε z hyp hL43 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact hodd _ f E Gp M₁ M₂ Y β M ε z hyp hL43 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

theorem burnsideF4m_F_4_38_of_rest (hodd : burnsideF4m_OddIndexInputRest) : F_4_38 :=
  burnsideF4j_F_4_38_of_rest (burnsideF4m_oddIndexInputRest_j hodd) burnsideF4m_genByTwoRest

end F433Un

end CFSG.ASVolI
