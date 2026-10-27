module

public import CFSG.LieType.Simplicity.Basic
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Simplicity.ExceptionalConverse
public import CFSG.Milestones.FAM_sporadic_converse

public section

namespace CFSG.Milestones

theorem cat_converse
    (G : Type) [Group G] (h : Blueprint.Catalog G) :
    Finite G ∧ IsSimpleGroup G := by
  have drop (h : Finite G ∧ Nontrivial G ∧ IsSimpleGroup G) : Finite G ∧ IsSimpleGroup G :=
    ⟨h.1, h.2.2⟩
  unfold Blueprint.Catalog at h
  rcases h with h | h | h | h | h
  · exact drop (LieType.Simplicity.fam_prime_cyclic_converse G h)
  · exact drop (LieType.Simplicity.fam_alternating_converse G h)
  · exact drop (LieType.Simplicity.fam_classical_converse G h)
  · exact drop (LieType.Simplicity.fam_exceptional_converse G h)
  · exact fam_sporadic_converse G h

end CFSG.Milestones
