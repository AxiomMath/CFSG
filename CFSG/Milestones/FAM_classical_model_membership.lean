module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Models

public section

universe u v w

namespace CFSG.Milestones

@[expose] def ClassicalRep (G : Type) [Group G] : Prop :=
  ∃ (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ),
    Assembly.LowTwoRank.StatedClassicalModel G t n p f

theorem fam_classical_model_membership_alltags (G : Type) [Group G] :
    ClassicalRep G ↔ ∃ (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ),
      Assembly.LowTwoRank.StatedClassicalModel G t n p f := Iff.rfl

theorem statedClassicalModel_tag_mem (G : Type) [Group G]
    (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ)
    (h : Assembly.LowTwoRank.StatedClassicalModel G t n p f) :
    t ∈ ({.PSL, .PSU, .PSp, .POmegaOdd, .POmegaPlus, .POmegaMinus} :
      Set Assembly.LowTwoRank.StatedLieTag) := by
  cases t with
  | PSL => exact .inl rfl
  | PSU => exact .inr (.inl rfl)
  | PSp => exact .inr (.inr (.inl rfl))
  | POmegaOdd => exact .inr (.inr (.inr (.inl rfl)))
  | POmegaPlus => exact .inr (.inr (.inr (.inr (.inl rfl))))
  | POmegaMinus => exact .inr (.inr (.inr (.inr (.inr rfl))))
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4
  | twistedB2 | twistedG2 | twistedF4 | Tits => exact h.2.elim

theorem fam_classical_model_membership (G : Type) [Group G] :
    ClassicalRep G ↔ ∃ t : Assembly.LowTwoRank.StatedLieTag,
      t ∈ ({.PSL, .PSU, .PSp, .POmegaOdd, .POmegaPlus, .POmegaMinus} :
        Set Assembly.LowTwoRank.StatedLieTag) ∧
      ∃ n p f : ℕ, Assembly.LowTwoRank.StatedClassicalModel G t n p f := by
  constructor
  · rintro ⟨t, n, p, f, h⟩
    exact ⟨t, statedClassicalModel_tag_mem G t n p f h, n, p, f, h⟩
  · rintro ⟨t, -, n, p, f, h⟩
    exact ⟨t, n, p, f, h⟩

end CFSG.Milestones
