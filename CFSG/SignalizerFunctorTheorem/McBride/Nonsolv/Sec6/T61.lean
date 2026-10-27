module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T613
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T61.Maximal
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T61.Centralizer

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem typeB_of_core
    (h : Counterexample p A θ) {E K : Subgroup G}
    (core : TypeBCore p A θ E K) : TypeB p A θ E K :=
  { toTypeBCore := core
    maximal := h.maximal_of_core core
    wreath_F' := h.wreath_F'_of_core core }

theorem theorem_6_1
    (h : Counterexample p A θ) :
    (TypeA p A θ ∨ ∃ E K : Subgroup G, TypeB p A θ E K) ∧ sSup (Msig p A θ) ⊔ A = ⊤ ∧
      zOf (sSup (Msig p A θ)) = ⊥ := by
  refine ⟨?_, h.generation, h.lemma_6_4⟩
  by_cases hS : sSet p A θ 1 = ∅
  · exact Or.inl (h.theorem_6_13 hS)
  · obtain ⟨E, K, -, core⟩ := h.theorem_6_14 (Set.nonempty_iff_ne_empty.mpr hS)
    exact Or.inr ⟨E, K, h.typeB_of_core core⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
