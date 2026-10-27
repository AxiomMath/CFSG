module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.H13.A6

namespace A7F

open Equiv Equiv.Perm

abbrev a7 : Perm (Fin 7) := swap 0 1 * swap 2 3

abbrev b7 : Perm (Fin 7) := swap 0 2 * swap 3 4

theorem a7_mem : a7 ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]; decide

theorem b7_mem : b7 ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]; decide

theorem a7_sq : a7 * a7 = 1 := by decide

theorem b7_sq : b7 * b7 = 1 := by decide

theorem ab7_pow_five : (a7 * b7) ^ 5 = 1 := by decide

theorem ab7_ne_one : a7 * b7 ≠ 1 := by decide

theorem ab7_ne_ba7 : a7 * b7 ≠ b7 * a7 := by decide

theorem support_card_of_inv {σ : Perm (Fin 7)} (hσ : sign σ = 1) (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    σ.support.card = 4 := by
  have hpow : σ ^ 2 = 1 := by rw [pow_two]; exact h2
  have htypes : ∀ n ∈ σ.cycleType, n = 2 := (Equiv.Perm.pow_prime_eq_one_iff).mp hpow
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate_card.2 htypes
  have hsum : σ.support.card = 2 * Multiset.card σ.cycleType := by
    rw [← Equiv.Perm.sum_cycleType, hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm,
      Multiset.card_replicate]
  have hle : σ.support.card ≤ 7 := by
    have := σ.support.card_le_univ
    simpa using this
  have hsign := hσ
  rw [Equiv.Perm.sign_of_cycleType, hrep] at hsign
  simp only [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hsign
  set c := Multiset.card σ.cycleType with hc
  have hc3 : c ≤ 3 := by omega
  have hc0 : c ≠ 0 := by
    intro h0
    apply h1
    rw [← Equiv.Perm.card_cycleType_eq_zero]
    exact h0
  interval_cases c
  · exact absurd rfl hc0
  · exact absurd hsign (by decide)
  · omega
  · exact absurd hsign (by decide)

theorem isConj_inv (σ : alternatingGroup (Fin 7)) (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    ∃ γ : alternatingGroup (Fin 7), γ * σ * γ⁻¹ = ⟨a7, a7_mem⟩ := by
  have hσ2 : (σ : Perm (Fin 7)) * σ = 1 := by
    have := congrArg Subtype.val h2
    simpa using this
  have hσ1 : (σ : Perm (Fin 7)) ≠ 1 := fun h => h1 (Subtype.ext h)
  have hc := support_card_of_inv (mem_alternatingGroup.1 σ.2) hσ2 hσ1
  have hca := support_card_of_inv (mem_alternatingGroup.1 a7_mem) a7_sq (by decide)
  have htype : ∀ τ : Perm (Fin 7), τ * τ = 1 → τ.support.card = 4 →
      τ.cycleType = {2, 2} := by
    intro τ hτ hτ4
    have hpow : τ ^ 2 = 1 := by rw [pow_two]; exact hτ
    have htypes : ∀ n ∈ τ.cycleType, n = 2 := (Equiv.Perm.pow_prime_eq_one_iff).mp hpow
    have hrep : τ.cycleType = Multiset.replicate (Multiset.card τ.cycleType) 2 :=
      Multiset.eq_replicate_card.2 htypes
    have hsum : τ.support.card = 2 * Multiset.card τ.cycleType := by
      rw [← Equiv.Perm.sum_cycleType, hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm,
        Multiset.card_replicate]
    rw [hrep, show Multiset.card τ.cycleType = 2 by omega]
    rfl
  have hconj : IsConj (σ : Perm (Fin 7)) a7 :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr ((htype _ hσ2 hc).trans (htype _ a7_sq hca).symm)
  have hsupp : (σ : Perm (Fin 7)).support.card + 2 ≤ Fintype.card (Fin 7) := by
    rw [hc]; decide
  have h := alternatingGroup.isConj_of (σ := σ) (τ := ⟨a7, a7_mem⟩) hconj hsupp
  obtain ⟨γ, hγ⟩ := isConj_iff.mp h
  exact ⟨γ, hγ⟩

theorem card_dvd_four {B : Subgroup (Perm (Fin 7))} (hBA : B ≤ alternatingGroup (Fin 7))
    (hB2 : ∀ b ∈ B, b * b = 1) : Nat.card B ∣ 4 := by
  classical
  have hfix : ∀ b : ↥B, Fintype.card (MulAction.fixedBy (Fin 7) b) =
      if b = 1 then 7 else 3 := by
    intro b
    have e : Fintype.card (MulAction.fixedBy (Fin 7) b) =
        Fintype.card (Function.fixedPoints (b : Perm (Fin 7))) :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
    rw [e, Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType]
    split_ifs with h1
    · rw [h1]; simp
    · have hb1 : (b : Perm (Fin 7)) ≠ 1 := fun h => h1 (Subtype.ext h)
      rw [support_card_of_inv (mem_alternatingGroup.1 (hBA b.2)) (hB2 b b.2) hb1]
      simp
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group ↥B (Fin 7)
  have hsum : ∑ b : ↥B, Fintype.card (MulAction.fixedBy (Fin 7) b) =
      3 * Fintype.card ↥B + 4 := by
    rw [Finset.sum_congr rfl fun b _ => hfix b, Finset.sum_ite, Finset.sum_const,
      Finset.sum_const]
    have hfilt : (Finset.univ.filter fun b : ↥B => b = 1) = {1} := by
      ext b; simp
    have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun b : ↥B => b = 1)
    rw [hfilt, Finset.card_singleton, Finset.card_univ] at hcard
    rw [hfilt, Finset.card_singleton, smul_eq_mul, smul_eq_mul]
    omega
  rw [hsum] at hburn
  set n := Fintype.card (Quotient (MulAction.orbitRel (↥B) (Fin 7))) with hn
  have hpos : 0 < Fintype.card ↥B := Fintype.card_pos
  rw [Nat.card_eq_fintype_card]
  have h4 : (n - 3) * Fintype.card ↥B = 4 := by
    have hn3 : 3 ≤ n := by
      by_contra h
      push Not at h
      have : n * Fintype.card ↥B ≤ 2 * Fintype.card ↥B := Nat.mul_le_mul_right _ (by omega)
      omega
    rw [Nat.sub_mul]
    omega
  exact ⟨n - 3, by rw [← h4, mul_comm]⟩

end A7F

end CFSG.Quasithin.H13.A6
