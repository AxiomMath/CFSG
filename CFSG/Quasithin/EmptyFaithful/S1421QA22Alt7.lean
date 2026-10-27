module

public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.Alt7

open Equiv Equiv.Perm

@[expose] def g5 : Perm (Fin 7) := c[0, 1, 2, 3, 4]

@[expose] def g5six : Perm (Fin 6) := c[0, 1, 2, 3, 4]

set_option maxRecDepth 100000 in
theorem comm_g5 : ∀ σ : Perm (Fin 7), σ * σ = 1 → σ * g5 = g5 * σ → σ = 1 ∨ σ = swap 5 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem comm_g5six : ∀ σ : Perm (Fin 6), σ * σ = 1 → σ * g5six = g5six * σ → σ = 1 := by
  decide +kernel

theorem cycleType_eq_five {n : ℕ} (hn : n ≤ 9) {g : Perm (Fin n)} (hg : orderOf g = 5) :
    g.cycleType = {5} := by
  have hne : g ≠ 1 := by
    rintro rfl
    simp at hg
  have hmem : ∀ m ∈ g.cycleType, m = 5 := by
    intro m hm
    have h1 : m ∣ 5 := hg ▸ dvd_of_mem_cycleType hm
    have h2 := two_le_of_mem_cycleType hm
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp h1 with h | h
    · omega
    · exact h
  have hrep : g.cycleType = Multiset.replicate (Multiset.card g.cycleType) 5 :=
    Multiset.eq_replicate_card.mpr hmem
  have hsum : g.cycleType.sum = g.support.card := sum_cycleType g
  have hsupp : g.support.card ≤ n := by
    have := Finset.card_le_univ g.support
    simpa using this
  have hcard : Multiset.card g.cycleType = 1 := by
    have hpos : Multiset.card g.cycleType ≠ 0 := by
      intro h0
      apply hne
      rw [← cycleType_eq_zero]
      exact Multiset.card_eq_zero.mp h0
    have : g.cycleType.sum = 5 * Multiset.card g.cycleType := by
      rw [hrep]
      simp [Multiset.sum_replicate, mul_comm]
    rw [this] at hsum
    omega
  rw [hrep, hcard]
  rfl

set_option maxRecDepth 100000 in
theorem orderOf_g5 : orderOf g5 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine orderOf_eq_prime ?_ ?_
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
theorem orderOf_g5six : orderOf g5six = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine orderOf_eq_prime ?_ ?_
  · decide +kernel
  · decide +kernel

theorem perm7_comm_five {g σ : Perm (Fin 7)} (hg : orderOf g = 5) (hσ : σ * σ = 1)
    (hc : σ * g = g * σ) : σ = 1 ∨ σ.IsSwap := by
  have hconj : IsConj g5 g :=
    (isConj_iff_cycleType_eq).mpr (by
      rw [cycleType_eq_five (by norm_num) hg, cycleType_eq_five (by norm_num) orderOf_g5])
  obtain ⟨π, hπ⟩ := isConj_iff.mp hconj
  have h1 : (π⁻¹ * σ * π) * (π⁻¹ * σ * π) = 1 := by
    calc (π⁻¹ * σ * π) * (π⁻¹ * σ * π) = π⁻¹ * (σ * σ) * π := by group
      _ = 1 := by rw [hσ]; group
  have h2 : (π⁻¹ * σ * π) * g5 = g5 * (π⁻¹ * σ * π) := by
    have hg5 : g5 = π⁻¹ * g * π := by rw [← hπ]; group
    calc (π⁻¹ * σ * π) * g5 = π⁻¹ * (σ * g) * π := by rw [hg5]; group
      _ = π⁻¹ * (g * σ) * π := by rw [hc]
      _ = g5 * (π⁻¹ * σ * π) := by rw [hg5]; group
  rcases comm_g5 _ h1 h2 with h | h
  · left
    have : σ = π * (π⁻¹ * σ * π) * π⁻¹ := by group
    rw [this, h]
    group
  · right
    have : σ = π * (π⁻¹ * σ * π) * π⁻¹ := by group
    rw [this, h, ← swap_apply_apply]
    exact ⟨π 5, π 6, by simp, rfl⟩

theorem perm6_comm_five {g σ : Perm (Fin 6)} (hg : orderOf g = 5) (hσ : σ * σ = 1)
    (hc : σ * g = g * σ) : σ = 1 := by
  have hconj : IsConj g5six g :=
    (isConj_iff_cycleType_eq).mpr (by
      rw [cycleType_eq_five (by norm_num) hg, cycleType_eq_five (by norm_num) orderOf_g5six])
  obtain ⟨π, hπ⟩ := isConj_iff.mp hconj
  have h1 : (π⁻¹ * σ * π) * (π⁻¹ * σ * π) = 1 := by
    calc (π⁻¹ * σ * π) * (π⁻¹ * σ * π) = π⁻¹ * (σ * σ) * π := by group
      _ = 1 := by rw [hσ]; group
  have h2 : (π⁻¹ * σ * π) * g5six = g5six * (π⁻¹ * σ * π) := by
    have hg5 : g5six = π⁻¹ * g * π := by rw [← hπ]; group
    calc (π⁻¹ * σ * π) * g5six = π⁻¹ * (σ * g) * π := by rw [hg5]; group
      _ = π⁻¹ * (g * σ) * π := by rw [hc]
      _ = g5six * (π⁻¹ * σ * π) := by rw [hg5]; group
  have h := comm_g5six _ h1 h2
  have : σ = π * (π⁻¹ * σ * π) * π⁻¹ := by group
  rw [this, h]
  group

theorem false_of_alt6_swap {σ : Perm (Fin 6)} (hσ : σ.IsSwap) {a : alternatingGroup (Fin 6)}
    (ha : orderOf a = 5) (hc : (a : Perm (Fin 6)) * σ = σ * (a : Perm (Fin 6))) : False := by
  have ha' : orderOf (a : Perm (Fin 6)) = 5 := by rw [Subgroup.orderOf_coe]; exact ha
  obtain ⟨x, y, hxy, hs⟩ := hσ
  have hσ2 : σ * σ = 1 := by rw [hs]; exact swap_mul_self x y
  have h1 := perm6_comm_five ha' hσ2 hc.symm
  rw [hs] at h1
  exact hxy (Equiv.swap_eq_one_iff.mp h1)

theorem false_of_alt7_inner {t g : alternatingGroup (Fin 7)} (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hg : orderOf g = 5) (hc : t * g = g * t) : False := by
  have hg' : orderOf (g : Perm (Fin 7)) = 5 := by rw [Subgroup.orderOf_coe]; exact hg
  have ht2' : (t : Perm (Fin 7)) * (t : Perm (Fin 7)) = 1 := by
    rw [← Subgroup.coe_mul, ht2]; rfl
  have hc' : (t : Perm (Fin 7)) * (g : Perm (Fin 7)) = (g : Perm (Fin 7)) * (t : Perm (Fin 7)) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hc]
  rcases perm7_comm_five hg' ht2' hc' with h | h
  · apply ht1
    exact Subtype.ext h
  · obtain ⟨x, y, hxy, hs⟩ := h
    have h1 : sign (t : Perm (Fin 7)) = -1 := by rw [hs]; exact sign_swap hxy
    have h2 : sign (t : Perm (Fin 7)) = 1 := (mem_alternatingGroup.mp t.2)
    rw [h1] at h2
    exact absurd h2 (by decide)

theorem false_of_alt7_cycle {σ : Perm (Fin 7)} (hσ : σ.cycleType = {2, 2, 2})
    {a : alternatingGroup (Fin 7)} (ha : orderOf a = 5)
    (hc : (a : Perm (Fin 7)) * σ = σ * (a : Perm (Fin 7))) : False := by
  have ha' : orderOf (a : Perm (Fin 7)) = 5 := by rw [Subgroup.orderOf_coe]; exact ha
  have hord : orderOf σ = 2 := by
    rw [← lcm_cycleType, hσ]
    decide
  have hσ2 : σ * σ = 1 := by
    rw [← sq]
    exact hord ▸ pow_orderOf_eq_one σ
  rcases perm7_comm_five ha' hσ2 hc.symm with h | h
  · rw [h] at hσ
    simp at hσ
  · rw [isSwap_iff_cycleType.mp h] at hσ
    exact absurd hσ (by decide)

end CFSG.Quasithin.Alt7
