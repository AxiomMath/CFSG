module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinG

public section

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm

theorem cycleType_swap_fin {a b : Fin 6} (h : a ≠ b) : (swap a b).cycleType = {2} := by
  rw [(isCycle_swap h).cycleType, card_support_swap h]

theorem cycleType_triple_swap :
    (swap (0 : Fin 6) 1 * swap 2 3 * swap 4 5).cycleType = {2, 2, 2} := by
  have d1 : Disjoint (swap (0 : Fin 6) 1) (swap 2 3) := show ∀ x : Fin 6, _ ∨ _ by decide
  have d2 : Disjoint (swap (0 : Fin 6) 1 * swap 2 3) (swap 4 5) := show ∀ x : Fin 6, _ ∨ _ by decide
  rw [d2.cycleType_mul, d1.cycleType_mul, cycleType_swap_fin (by decide),
    cycleType_swap_fin (by decide), cycleType_swap_fin (by decide)]
  rfl

theorem cycleType_of_sq_eq_one (s : Perm (Fin 6)) (hs : s * s = 1) :
    ∃ k, k ≤ 3 ∧ s.cycleType = Multiset.replicate k 2 := by
  have hord : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hs)
  have hall : ∀ n ∈ s.cycleType, n = 2 := fun n hn => by
    have h1 := (Perm.dvd_of_mem_cycleType hn).trans hord
    have h2 := Perm.two_le_of_mem_cycleType hn
    exact le_antisymm (Nat.le_of_dvd (by norm_num) h1) h2
  have hrep : s.cycleType = Multiset.replicate (Multiset.card s.cycleType) 2 :=
    Multiset.eq_replicate_card.mpr hall
  refine ⟨Multiset.card s.cycleType, ?_, hrep⟩
  have hsum := Perm.sum_cycleType_le s
  have hs' : s.cycleType.sum = 2 * Multiset.card s.cycleType := by
    conv_lhs => rw [hrep]
    simp [Multiset.sum_replicate, mul_comm]
  simp only [Fintype.card_fin] at hsum
  omega

theorem odd_invol_cent3 (s : Perm (Fin 6)) (hs : s * s = 1) (hsg : sign s = -1) :
    ∃ g : Perm (Fin 6), sign g = 1 ∧ g * g * g = 1 ∧ g ≠ 1 ∧ g * s = s * g := by
  obtain ⟨k, hk3, hct⟩ := cycleType_of_sq_eq_one s hs
  have hsign := sign_of_cycleType s
  rw [hct] at hsign
  simp only [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hsign
  rw [hsg] at hsign
  interval_cases k
  · simp at hsign
  ·
    have hconj : IsConj (swap (0 : Fin 6) 1) s :=
      isConj_iff_cycleType_eq.mpr (by rw [hct, cycleType_swap_fin (by decide)]; rfl)
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    refine ⟨c * (swap 2 3 * swap 3 4) * c⁻¹, ?_, ?_, ?_, ?_⟩
    · simp [sign_mul, sign_inv]
    · calc c * (swap 2 3 * swap 3 4) * c⁻¹ * (c * (swap 2 3 * swap 3 4) * c⁻¹) *
          (c * (swap 2 3 * swap 3 4) * c⁻¹)
          = c * ((swap 2 3 * swap 3 4) * (swap 2 3 * swap 3 4) * (swap 2 3 * swap 3 4)) * c⁻¹ := by
            group
        _ = 1 := by
          have : (swap (2 : Fin 6) 3 * swap 3 4) * (swap 2 3 * swap 3 4) * (swap 2 3 * swap 3 4) = 1 := by
            decide
          rw [this]; group
    · intro h
      have h2 : swap (2 : Fin 6) 3 * swap 3 4 = 1 := by
        have := congrArg (fun t => c⁻¹ * t * c) h
        simpa [mul_assoc] using this
      revert h2; decide
    · rw [← hc]
      have hcomm : (swap (2 : Fin 6) 3 * swap 3 4) * swap 0 1 = swap 0 1 * (swap 2 3 * swap 3 4) := by
        decide
      calc c * (swap 2 3 * swap 3 4) * c⁻¹ * (c * swap 0 1 * c⁻¹)
          = c * ((swap 2 3 * swap 3 4) * swap 0 1) * c⁻¹ := by group
        _ = c * (swap 0 1 * (swap 2 3 * swap 3 4)) * c⁻¹ := by rw [hcomm]
        _ = c * swap 0 1 * c⁻¹ * (c * (swap 2 3 * swap 3 4) * c⁻¹) := by group
  · exfalso
    revert hsign
    decide
  ·
    have hconj : IsConj (swap (0 : Fin 6) 1 * swap 2 3 * swap 4 5) s :=
      isConj_iff_cycleType_eq.mpr (by rw [hct, cycleType_triple_swap]; rfl)
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    refine ⟨c * (swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5) * c⁻¹, ?_, ?_, ?_, ?_⟩
    · simp [sign_mul, sign_inv]
    · calc c * (swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5) * c⁻¹ *
          (c * (swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5) * c⁻¹) *
          (c * (swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5) * c⁻¹)
          = c * ((swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5) * (swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5) *
              (swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5)) * c⁻¹ := by group
        _ = 1 := by
          have : (swap (0 : Fin 6) 2 * swap 2 4 * swap 1 3 * swap 3 5) *
              (swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5) *
              (swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5) = 1 := by decide
          rw [this]; group
    · intro h
      have h2 : swap (0 : Fin 6) 2 * swap 2 4 * swap 1 3 * swap 3 5 = 1 := by
        have := congrArg (fun t => c⁻¹ * t * c) h
        simpa [mul_assoc] using this
      revert h2; decide
    · rw [← hc]
      have hcomm : (swap (0 : Fin 6) 2 * swap 2 4 * swap 1 3 * swap 3 5) *
          (swap 0 1 * swap 2 3 * swap 4 5) =
          (swap 0 1 * swap 2 3 * swap 4 5) * (swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5) := by
        decide
      calc c * (swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5) * c⁻¹ *
          (c * (swap 0 1 * swap 2 3 * swap 4 5) * c⁻¹)
          = c * ((swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5) * (swap 0 1 * swap 2 3 * swap 4 5)) * c⁻¹ := by
            group
        _ = c * ((swap 0 1 * swap 2 3 * swap 4 5) * (swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5)) * c⁻¹ := by
            rw [hcomm]
        _ = c * (swap 0 1 * swap 2 3 * swap 4 5) * c⁻¹ *
            (c * (swap 0 2 * swap 2 4 * swap 1 3 * swap 3 5) * c⁻¹) := by group

end CFSG.Quasithin.A6Fin
