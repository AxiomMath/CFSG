module

public import CFSG.Milestones.ASVolI.F431.ASp2Facts
public import CFSG.Milestones.ASVolI.F431.BCoreTop

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section NonU2

set_option linter.unusedSectionVars false

variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4m_odd_index_nonU2 (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z)
    (hU : ¬ ((κ = .U4 ∨ κ = .U5) ∧ f = 1)) : Odd Gp.index := by
  have hf1 : 1 ≤ f := by
    have hm := hyp.amalgam.model
    cases κ <;> first
      | exact hm.2.1
      | (obtain ⟨-, hfo, -⟩ := hm; exact hfo.pos)
      | (obtain ⟨-, hf, -⟩ := hm; omega)
  have hone : Gp = ⊤ → Odd Gp.index := fun h => by
    rw [h, Subgroup.index_top]
    exact odd_one
  cases κ
  · exact burnsideF4d_L3_odd (burnsideF4d_L3_two_le_f hyp) hyp
  · by_cases hf2 : 2 ≤ f
    · exact burnsideF4m_odd_index_Sp4_of burnsideF4m_lieCoreSp hyp hf2
    · have hf : f = 1 := by omega
      subst hf
      exact hone (burnsideF4m_topSp2 E Gp M₁ M₂ hyp.amalgam)
  · rcases Nat.even_or_odd f with he | ho
    · exact burnsideF4m_odd_index_G2_lie burnsideF4m_lieCoreInput hyp
        (by obtain ⟨k, rfl⟩ := he; omega)
    · by_cases h1 : f = 1
      · subst h1
        exact hone (burnsideF4m_top_G2two hyp.amalgam)
      · exact burnsideF4jb_odd_index_G2 hyp.amalgam ho (by omega)
  · rcases Nat.even_or_odd f with he | ho
    · exact burnsideF4m_odd_index_D4tw_lie burnsideF4m_lieCoreInput hyp
        (by obtain ⟨k, rfl⟩ := he; omega)
    · exact burnsideF4jb_odd_index_D4tw hyp.amalgam ho
  · by_cases hf3 : 3 ≤ f
    · exact burnsideF4j_odd_index_F4tw hyp.amalgam hf3
    · obtain ⟨-, -, h1 | h3⟩ := hyp.amalgam.model
      · have hf : f = 1 := h1.1
        subst hf
        exact hone (burnsideF4m_top_F4two hyp.amalgam)
      · exact absurd h3.1 hf3
  · by_cases hf2 : 2 ≤ f
    · exact burnsideF4m_odd_index_U4_lie burnsideF4m_lieCoreInput hyp hf2
    · exact absurd ⟨Or.inl rfl, by omega⟩ hU
  · by_cases hf2 : 2 ≤ f
    · exact burnsideF4m_odd_index_U5_lie' burnsideF4m_lieCoreInput hyp hf2
    · exact absurd ⟨Or.inr rfl, by omega⟩ hU
  · exact absurd rfl hyp.not_G2d
  · exact burnsideF4j_odd_index_Tits hyp.amalgam

end NonU2

end CFSG.ASVolI
