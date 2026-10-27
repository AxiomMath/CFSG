module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Perm.Centralizer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv Equiv.Perm Subgroup

theorem w85g_exists_odd_card_support {α : Type} [Fintype α] [DecidableEq α] {τ : Perm α}
    (hτ : τ * τ = 1) (hs : Perm.sign τ = -1) :
    ∃ j, Odd j ∧ τ.support.card = 2 * j := by
  have hτ2 : τ ^ 2 = 1 := by rwa [pow_two]
  obtain ⟨j, hj⟩ := Equiv.Perm.two_dvd_card_support hτ2
  refine ⟨j, ?_, hj⟩
  have hfix : Fintype.card α - Fintype.card (Function.fixedPoints τ) = τ.support.card := by
    have hle : τ.support.card ≤ Fintype.card α := by
      rw [← Equiv.Perm.sum_cycleType]
      exact τ.sum_cycleType_le
    rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType]
    omega
  have hsign := Equiv.Perm.sign_of_pow_two_eq_one hτ2
  rw [hs, hfix, hj, Nat.mul_div_cancel_left j (by norm_num : 0 < 2)] at hsign
  exact (neg_one_pow_eq_neg_one_iff_odd (by decide : (-1 : ℤˣ) ≠ 1)).mp hsign.symm

theorem w85g_mul_swap_commute_iff {α : Type} [DecidableEq α] {z : Perm α} {i j : α}
    (hij : i ≠ j) :
    z * swap i j = swap i j * z ↔ (z i = i ∧ z j = j) ∨ (z i = j ∧ z j = i) := by
  constructor
  · intro h
    have h1 : z j = swap i j (z i) := by
      have := congrArg (fun z : Perm α => z i) h
      simpa [Equiv.Perm.mul_apply] using this
    by_cases hi : z i = i
    · exact Or.inl ⟨hi, by rw [h1, hi, swap_apply_left]⟩
    · by_cases hj : z i = j
      · exact Or.inr ⟨hj, by rw [h1, hj, swap_apply_right]⟩
      · exfalso
        have hji : z j = z i := by rw [h1, swap_apply_of_ne_of_ne hi hj]
        exact hij (z.injective hji).symm
  · rintro (⟨hi, hj⟩ | ⟨hi, hj⟩)
    · have h := (Equiv.swap_apply_apply z i j).symm
      rw [hi, hj] at h
      exact mul_inv_eq_iff_eq_mul.mp h
    · have h := (Equiv.swap_apply_apply z i j).symm
      rw [hi, hj, swap_comm j i] at h
      exact mul_inv_eq_iff_eq_mul.mp h

theorem w85g_nat_card_centralizer_isSwap {n : ℕ} {τ : Perm (Fin n)} (h : τ.IsSwap) :
    Nat.card (Subgroup.centralizer ({τ} : Set (Perm (Fin n)))) = 2 * Nat.factorial (n - 2) := by
  rw [Equiv.Perm.nat_card_centralizer, Equiv.Perm.isSwap_iff_cycleType.mp h]
  simp [Nat.mul_comm]

theorem w85g_isSwap_of_sign_neg_one_card_le_five {n : ℕ} (hn : n ≤ 5) {τ : Perm (Fin n)}
    (hτ : τ * τ = 1) (hs : Perm.sign τ = -1) : τ.IsSwap := by
  obtain ⟨j, hoddj, hj⟩ := w85g_exists_odd_card_support hτ hs
  have hle : τ.support.card ≤ n := by simpa using Finset.card_le_univ τ.support
  obtain ⟨k, hk⟩ := hoddj
  have hj1 : j = 1 := by omega
  rw [hj1, mul_one] at hj
  exact Equiv.Perm.card_support_eq_two.mp hj

theorem w85g_exists_two_pairs {α : Type} [Fintype α] [DecidableEq α] {τ : Perm α}
    (hτ : τ * τ = 1) (h4 : 4 ≤ τ.support.card) :
    ∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      τ a = b ∧ τ b = a ∧ τ c = d ∧ τ d = c := by
  have hττ : ∀ x, τ (τ x) = x := by
    intro x
    have := congrArg (fun g : Perm α => g x) hτ
    simpa [Equiv.Perm.mul_apply] using this
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < τ.support.card)
  have hane : τ a ≠ a := (Equiv.Perm.mem_support).mp ha
  have hb : τ a ∈ τ.support :=
    (Equiv.Perm.mem_support).mpr (by rw [hττ]; exact Ne.symm hane)
  have hb_erase : τ a ∈ τ.support.erase a := by
    rw [Finset.mem_erase]
    exact ⟨hane, hb⟩
  have hcard : 0 < ((τ.support.erase a).erase (τ a)).card := by
    rw [Finset.card_erase_of_mem hb_erase, Finset.card_erase_of_mem ha]
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hcard
  rw [Finset.mem_erase] at hc
  obtain ⟨hcb, hc⟩ := hc
  rw [Finset.mem_erase] at hc
  obtain ⟨hca, hcsupp⟩ := hc
  have hτc : τ c ≠ c := (Equiv.Perm.mem_support).mp hcsupp
  refine ⟨a, τ a, c, τ c, Ne.symm hane, Ne.symm hca, ?_, Ne.symm hcb, ?_, Ne.symm hτc,
    rfl, hττ a, rfl, hττ c⟩
  · intro h
    have h' : τ a = c := by rw [h, hττ]
    exact hcb h'.symm
  · intro h
    have h' : a = c := by rw [← hττ a, h, hττ c]
    exact hca h'.symm

theorem w85g_exists_commuting_conj_four {α : Type} [Fintype α] [DecidableEq α] {τ : Perm α}
    (hτ : τ * τ = 1) (hs : Perm.sign τ = -1)
    {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hta : τ a = b) (htb : τ b = a) (htc : τ c = d) (htd : τ d = c) :
    ∃ c' ∈ alternatingGroup α, c' * τ * c'⁻¹ ≠ τ ∧
      τ * (c' * τ * c'⁻¹) = (c' * τ * c'⁻¹) * τ := by
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hconj : (swap a c * τ) * τ * (swap a c * τ)⁻¹ = swap a c * τ * swap a c := by
    rw [mul_inv_rev, Equiv.swap_inv, hτi]
    calc (swap a c * τ) * τ * (τ * swap a c)
        = swap a c * (τ * τ) * (τ * swap a c) := by group
      _ = swap a c * 1 * (τ * swap a c) := by rw [hτ]
      _ = swap a c * τ * swap a c := by group
  refine ⟨swap a c * τ, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hac, hs]
    decide
  · intro h
    rw [hconj] at h
    have h1 : (swap a c * τ * swap a c) a = d := by
      simp [Equiv.Perm.mul_apply, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne,
        Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd, Ne.symm hcd,
        hbc, hbd, hcd, hab, hac, had, hta, htb, htc, htd, hτi]
    rw [h, hta] at h1
    exact hbd h1
  · rw [hconj]
    have hcomm : swap a c * swap b d = swap b d * swap a c := by
      have hnd' : [a, c, b, d].Nodup := by simp [List.nodup_cons, Ne.symm hbc, *]
      exact (Equiv.Perm.disjoint_swap_swap hnd').commute
    have hX : τ * (swap a c * τ * swap a c) = swap b d * swap a c := by
      calc τ * (swap a c * τ * swap a c)
          = (τ * swap a c * τ) * swap a c := by group
        _ = (τ * swap a c * τ⁻¹) * swap a c := by rw [hτi]
        _ = swap (τ a) (τ c) * swap a c := by rw [Equiv.swap_apply_apply]
        _ = swap b d * swap a c := by rw [hta, htc]
    have hY : (swap a c * τ * swap a c) * τ = swap b d * swap a c := by
      calc (swap a c * τ * swap a c) * τ
          = swap a c * (τ * swap a c * τ) := by group
        _ = swap a c * (τ * swap a c * τ⁻¹) := by rw [hτi]
        _ = swap a c * swap (τ a) (τ c) := by rw [Equiv.swap_apply_apply]
        _ = swap a c * swap b d := by rw [hta, htc]
        _ = swap b d * swap a c := hcomm
    rw [hX, hY]

theorem w85g_exists_commuting_conj_swap {α : Type} [Fintype α] [DecidableEq α]
    {a b : α} (hab : a ≠ b) (h4 : 4 ≤ Fintype.card α) :
    ∃ c' ∈ alternatingGroup α, c' * swap a b * c'⁻¹ ≠ swap a b ∧
      swap a b * (c' * swap a b * c'⁻¹) = (c' * swap a b * c'⁻¹) * swap a b := by
  have hcard : 2 ≤ (Finset.univ \ ({a, b} : Finset α)).card := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Finset.card_pair hab]
    omega
  obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.mp
    (by omega : 1 < (Finset.univ \ ({a, b} : Finset α)).card)
  rw [Finset.mem_sdiff] at he hf
  obtain ⟨-, he⟩ := he
  obtain ⟨-, hf⟩ := hf
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he hf
  obtain ⟨hea, heb⟩ := he
  obtain ⟨hfa, hfb⟩ := hf
  have h1 : (swap a e * swap b f) * swap a b * (swap a e * swap b f)⁻¹ = swap e f := by
    rw [← Equiv.swap_apply_apply]
    simp [Equiv.Perm.mul_apply, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne,
      Ne.symm hea, Ne.symm heb, Ne.symm hef, Ne.symm hfa, Ne.symm hfb,
      hea, heb, hef, hfa, hfb, hab]
  refine ⟨swap a e * swap b f, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, map_mul,
      Equiv.Perm.sign_swap (Ne.symm hea), Equiv.Perm.sign_swap (Ne.symm hfb)]
    decide
  · intro h
    rw [h1] at h
    have h2 : swap e f a ≠ swap a b a := by
      rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hea) (Ne.symm hfa), Equiv.swap_apply_left]
      exact hab
    exact h2 (by rw [← h])
  · have hcomm : swap a b * swap e f = swap e f * swap a b := by
      have hnd : [e, f, a, b].Nodup := by
        simp [List.nodup_cons, Ne.symm hea, Ne.symm heb, Ne.symm hef, Ne.symm hfa,
          Ne.symm hfb, hab, *]
      exact (Equiv.Perm.disjoint_swap_swap hnd).commute.symm
    rw [h1]
    exact hcomm

end CFSG.LocalAnalysis.WeakClosure81

end
