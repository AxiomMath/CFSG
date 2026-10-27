module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.ASVolI.ChH

open Equiv

theorem cycleType_eq_two_or_two_two_two {x : Perm (Fin 8)} (h2 : x ^ 2 = 1)
    (hs : Perm.sign x = -1) : x.cycleType = {2} ∨ x.cycleType = {2, 2, 2} := by
  obtain ⟨k, hk⟩ : ∃ k, x.cycleType = Multiset.replicate k 2 :=
    ⟨_, Perm.cycleType_of_pow_prime_eq_one (p := 2) h2⟩
  have hle := Perm.sum_cycleType_le x
  have hsign := Perm.sign_of_cycleType x
  rw [hk] at hle hsign
  simp only [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul,
    Fintype.card_fin] at hle hsign
  rw [hs] at hsign
  have hk4 : k ≤ 4 := by omega
  rw [hk]
  obtain rfl | rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  · exact absurd hsign (by decide)
  · exact Or.inl rfl
  · exact absurd hsign (by decide)
  · exact Or.inr rfl
  · exact absurd hsign (by decide)

theorem cycleType_swap_zero_one : (Equiv.swap (0 : Fin 8) 1).cycleType = {2} :=
  Perm.isSwap_iff_cycleType.mp (Perm.swap_isSwap_iff.mpr (by decide))

theorem cycleType_swap_triple :
    (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3 * Equiv.swap 4 5).cycleType = {2, 2, 2} := by
  have hd : Perm.Disjoint (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3) (Equiv.swap 4 5) :=
    Perm.Disjoint.mul_left (Perm.disjoint_swap_swap (by decide))
      (Perm.disjoint_swap_swap (by decide))
  rw [hd.cycleType_mul, Perm.cycleType_swap_mul_swap_of_nodup (by decide),
    Perm.isSwap_iff_cycleType.mp (Perm.swap_isSwap_iff.mpr (by decide))]
  rfl

theorem orderOf_swap_zero_one : orderOf (Equiv.swap (0 : Fin 8) 1) = 2 :=
  Perm.IsSwap.orderOf (Perm.swap_isSwap_iff.mpr (by decide))

theorem orderOf_swap_triple :
    orderOf (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3 * Equiv.swap 4 5) = 2 := by
  rw [← Perm.lcm_cycleType, cycleType_swap_triple]
  rfl

theorem sign_swap_zero_one : Perm.sign (Equiv.swap (0 : Fin 8) 1) = -1 :=
  Perm.sign_swap (by decide)

theorem sign_swap_triple :
    Perm.sign (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3 * Equiv.swap 4 5) = -1 := by
  rw [map_mul, map_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide),
    Perm.sign_swap (by decide)]
  decide

end CFSG.ASVolI.ChH
