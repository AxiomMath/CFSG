module

public import CFSG.Milestones.ASVolI.F431.J2
public import CFSG.Milestones.ASVolI.F431.JSp2
public import CFSG.Milestones.ASVolI.F431.JOdd

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Final

set_option linter.unusedSectionVars false

@[expose] def burnsideF4j_GenByTwoInputRest : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ 2 f Gp M₁ M₂ → (κ = .G2 ∨ κ = .F4tw) → f = 1 → oPPrime 2 Gp = Gp

theorem burnsideF4j_genByTwo (hrest : burnsideF4j_GenByTwoInputRest) {κ : GLKind} {f : ℕ}
    {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ 2 f Gp M₁ M₂)
    (hG2d : κ ≠ .G2d) : oPPrime 2 Gp = Gp := by
  cases κ
  · exact burnsideF4jb_oPPrime_Gp_L3 hyp
  · exact burnsideF4jb_oPPrime_Gp_Sp4 hyp
  · by_cases hf2 : 2 ≤ f
    · exact burnsideF4jb_oPPrime_Gp_G2 hyp hf2
    · have hf1 : 1 ≤ f := hyp.model.2.1
      exact hrest _ f E Gp M₁ M₂ hyp (Or.inl rfl) (by omega)
  · exact burnsideF4jb_oPPrime_Gp_D4tw hyp
  · by_cases hf3 : 3 ≤ f
    · exact burnsideF4jb_oPPrime_Gp_F4tw hyp hf3
    · obtain ⟨-, -, h1 | h3⟩ := hyp.model
      · exact hrest _ f E Gp M₁ M₂ hyp (Or.inr rfl) h1.1
      · exact absurd h3.1 hf3
  · exact burnsideF4jb_oPPrime_Gp_U4 hyp
  · exact burnsideF4jb_oPPrime_Gp_U5 hyp
  · exact absurd rfl hG2d
  · exact burnsideF4jb_oPPrime_Gp_Tits hyp

@[expose] def burnsideF4j_OddIndexInputRest : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M →
    ((κ = .Sp4 ∧ (Even f ∨ f = 1)) ∨ (κ = .G2 ∧ (Even f ∨ f = 1)) ∨ (κ = .D4tw ∧ Even f) ∨
      (κ = .F4tw ∧ f = 1) ∨ κ = .U4 ∨ κ = .U5) → Odd Gp.index

theorem burnsideF4j_oddIndex (hrest : burnsideF4j_OddIndexInputRest) :
    burnsideF4j_OddIndexInput := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL43
  have hf1 : 1 ≤ f := by
    have hm := hyp.amalgam.model
    cases κ <;> first
      | exact hm.2.1
      | (obtain ⟨-, hfo, -⟩ := hm; exact hfo.pos)
      | (obtain ⟨-, hf, -⟩ := hm; omega)
  have hrest' := hrest κ f E Gp M₁ M₂ Y β M ε z hyp hL43
  cases κ
  · exact burnsideF4d_L3_odd (burnsideF4d_L3_two_le_f hyp) hyp
  · rcases Nat.even_or_odd f with he | ho
    · exact hrest' (Or.inl ⟨rfl, Or.inl he⟩)
    · by_cases h1 : f = 1
      · exact hrest' (Or.inl ⟨rfl, Or.inr h1⟩)
      · have hf3 : 3 ≤ f := by obtain ⟨k, rfl⟩ := ho; omega
        exact burnsideF4j_odd_index_Sp4 hyp.amalgam hf3 ho
  · rcases Nat.even_or_odd f with he | ho
    · exact hrest' (Or.inr (Or.inl ⟨rfl, Or.inl he⟩))
    · by_cases h1 : f = 1
      · exact hrest' (Or.inr (Or.inl ⟨rfl, Or.inr h1⟩))
      · exact burnsideF4jb_odd_index_G2 hyp.amalgam ho (by omega)
  · rcases Nat.even_or_odd f with he | ho
    · exact hrest' (Or.inr (Or.inr (Or.inl ⟨rfl, he⟩)))
    · exact burnsideF4jb_odd_index_D4tw hyp.amalgam ho
  · by_cases hf3 : 3 ≤ f
    · exact burnsideF4j_odd_index_F4tw hyp.amalgam hf3
    · obtain ⟨-, -, h1 | h3⟩ := hyp.amalgam.model
      · exact hrest' (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h1.1⟩))))
      · exact absurd h3.1 hf3
  · exact hrest' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact hrest' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  · exact absurd rfl hyp.not_G2d
  · exact burnsideF4j_odd_index_Tits hyp.amalgam

theorem burnsideF4j_F_4_38_of_rest (hodd : burnsideF4j_OddIndexInputRest)
    (hgen : burnsideF4j_GenByTwoInputRest) : F_4_38 := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL43 T hT
  exact burnsideF4j_F_4_38_inst hyp (burnsideF4j_oddIndex hodd κ f E Gp M₁ M₂ Y β M ε z hyp hL43)
    (burnsideF4j_genByTwo hgen hyp.amalgam hyp.not_G2d) hT

end Final

end CFSG.ASVolI
