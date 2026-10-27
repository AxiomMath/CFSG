module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

namespace CFSG.Sporadic.SchreierLemmas

open Equiv Equiv.Perm Nat

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem order_three_permutation_shape {u : Perm Ω} (hu : orderOf u = 3) :
    ∃ k : ℕ, 1 ≤ k ∧ 3 * k ≤ Fintype.card Ω ∧ u.cycleType = Multiset.replicate k 3 ∧
      u.cycleFactorsFinset.card = k ∧ (∀ c ∈ u.cycleFactorsFinset, c.IsThreeCycle) ∧
      sign u = 1 := by
  obtain ⟨k, hk⟩ := cycleType_prime_order (hu ▸ Nat.prime_three)
  rw [hu] at hk
  refine ⟨k + 1, by omega, ?_, hk, ?_, fun c hc => ?_, ?_⟩
  · have := sum_cycleType_le u
    rw [hk, Multiset.sum_replicate, smul_eq_mul] at this
    omega
  · have := congrArg Multiset.card (cycleType_def u)
    rw [hk, Multiset.card_replicate, Multiset.card_map] at this
    exact this.symm
  · have hmem : c.support.card ∈ u.cycleType := by
      rw [cycleType_def]
      exact Multiset.mem_map_of_mem (Finset.card ∘ support) hc
    rw [hk] at hmem
    rw [IsThreeCycle, (mem_cycleFactorsFinset_iff.1 hc).1.cycleType,
      Multiset.eq_of_mem_replicate hmem]
  · rw [sign_of_cycleType, hk, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul,
      show (k + 1) * 3 + (k + 1) = 2 * (2 * (k + 1)) by ring, pow_mul]
    simp

end CFSG.Sporadic.SchreierLemmas
