module

public import CFSG.Timmesfeld.Outcome
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Simplicity.ExceptionalConverse
public import CFSG.Sporadic.J2

public section

namespace CFSG.Timmesfeld

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem isSimpleGroup_of_lieModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel G t n p f) : IsSimpleGroup G := by
  rcases h with ⟨-, h⟩ | ⟨-, ht, h⟩ | ⟨-, ht, h⟩ | ⟨-, -, h⟩
  · exact (LieType.Simplicity.fam_classical_converse G
      ((Milestones.fam_classical_model_membership_alltags G).2 ⟨t, n, p, f, h⟩)).2.2
  · exact (LieType.Simplicity.fam_exceptional_converse G (.inl ⟨t, p, f, ht, h⟩)).2.2
  · exact (LieType.Simplicity.fam_exceptional_converse G (.inr (.inl ⟨t, p, f, ht, h⟩))).2.2
  · exact (LieType.Simplicity.fam_exceptional_converse G (.inr (.inr ⟨p, f, h⟩))).2.2

theorem isSimpleGroup_of_outcome {G : Type} [Group G] (h : Outcome G) : IsSimpleGroup G := by
  rcases h with ⟨_, _, -, -, h⟩ | ⟨_, _, -, -, h⟩ | ⟨_, _, -, -, h | h⟩ | ⟨_, -, h⟩ |
      ⟨_, -, _, -, h⟩ | h | h | h
  iterate 7 exact isSimpleGroup_of_lieModel h
  · obtain ⟨e⟩ := h
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  · obtain ⟨e⟩ := h
    have : IsSimpleGroup (NativeSporadic.Carrier .J2) := Sporadic.J2.isSimpleGroup_J2
    exact e.isSimpleGroup

end CFSG.Timmesfeld
