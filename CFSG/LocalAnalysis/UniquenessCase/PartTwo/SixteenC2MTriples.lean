module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def s16c2m_Triples (N : Type) [CommGroup N] : Subgroup (Fin 3 → N) where
  carrier := {t | ∏ i, t i = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Pi.mul_apply, Finset.prod_mul_distrib] at ha hb ⊢
    rw [ha, hb, mul_one]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Pi.inv_apply, Finset.prod_inv_distrib] at ha ⊢
    rw [ha, inv_one]

theorem s16c2m_mem_Triples_iff {N : Type} [CommGroup N] (t : Fin 3 → N) :
    t ∈ s16c2m_Triples N ↔ t 0 * t 1 * t 2 = 1 := by
  change ∏ i, t i = 1 ↔ _
  rw [Fin.prod_univ_three]

theorem s16c2m_Triples_two_eq {N : Type} [CommGroup N] {t : Fin 3 → N} (ht : t ∈ s16c2m_Triples N) :
    t 2 = (t 0 * t 1)⁻¹ := by
  rw [s16c2m_mem_Triples_iff] at ht
  exact eq_inv_of_mul_eq_one_right ht

@[expose] def s16c2m_tripleEquiv (N : Type) [CommGroup N] : s16c2m_Triples N ≃* N × N where
  toFun t := ((t : Fin 3 → N) 0, (t : Fin 3 → N) 1)
  invFun p := ⟨![p.1, p.2, (p.1 * p.2)⁻¹], by
    rw [s16c2m_mem_Triples_iff]
    simp⟩
  left_inv t := by
    refine Subtype.ext (funext fun i => ?_)
    have h2 := s16c2m_Triples_two_eq t.2
    fin_cases i
    · rfl
    · rfl
    · exact h2.symm
  right_inv p := by simp
  map_mul' a b := rfl

theorem s16c2m_card_Triples (N : Type) [CommGroup N] :
    Nat.card (s16c2m_Triples N) = Nat.card N ^ 2 := by
  rw [Nat.card_congr (s16c2m_tripleEquiv N).toEquiv, Nat.card_prod, sq]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
