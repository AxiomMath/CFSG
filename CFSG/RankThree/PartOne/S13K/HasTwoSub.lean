module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartOne

open scoped commutatorElement

@[expose] def HasTwoSub {G : Type} [Group G] (E K : Subgroup G) : Prop :=
  ∃ S : Subgroup G, S ≤ K ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ E ≤ Subgroup.normalizer (S : Set G) ∧ S = ⁅S, E⁆

theorem HasTwoSub.mono {G : Type} [Group G] {E K K' : Subgroup G} (hKK : K ≤ K')
    (h : HasTwoSub E K) : HasTwoSub E K' := by
  obtain ⟨S, hSK, h2⟩ := h
  exact ⟨S, hSK.trans hKK, h2⟩

end CFSG.RankThree.PartOne
