module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4D

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem pow_three_units (hK : Nat.card K = 4) (a : Kˣ) : a ^ 3 = 1 := by
  have h3 : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have h := pow_card_eq_one' (x := a)
  rwa [h3] at h

omit [Finite K] in
theorem inv_ne_self_units (hK : Nat.card K = 4) {a : Kˣ} (ha : a ≠ 1) : a⁻¹ ≠ a := by
  intro h
  apply ha
  have h2 : a ^ 2 = 1 := by
    rw [sq]
    nth_rw 1 [← h]
    exact inv_mul_cancel a
  have h3 := pow_three_units hK a
  calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, mul_one]

theorem units_cases (hK : Nat.card K = 4) {a : Kˣ} (ha : a ≠ 1) (b : Kˣ) :
    b = 1 ∨ b = a ∨ b = a⁻¹ := by
  classical
  have := Fintype.ofFinite Kˣ
  have hai : a⁻¹ ≠ 1 := fun h => ha (inv_eq_one.mp h)
  have hcard : ({1, a, a⁻¹} : Finset Kˣ).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (inv_ne_self_units hK ha).symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm ha, Ne.symm hai⟩
  have huniv : ({1, a, a⁻¹} : Finset Kˣ) = Finset.univ := Finset.eq_univ_of_card _ (by
    rw [hcard, ← Nat.card_eq_fintype_card, Nat.card_units, hK])
  have hb : b ∈ ({1, a, a⁻¹} : Finset Kˣ) := huniv ▸ Finset.mem_univ b
  simpa using hb

theorem tS_cases (hK : Nat.card K = 4) {E : Subgroup (Fin 2 → Kˣ)} (hE : Nat.card ↥E = 3) :
    E = tSa K ∨ E = tSb K ∨ E = tSc K ∨ E = tSd K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  obtain ⟨e, heE, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
    by_contra h
    push Not at h
    have hb : E = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (h x hx)
    rw [hb, Subgroup.card_bot] at hE
    norm_num at hE
  have hord : orderOf e = 3 := by
    have he3 : e ^ 3 = 1 := funext fun i => by rw [Pi.pow_apply]; exact pow_three_units hK (e i)
    exact orderOf_eq_prime he3 he1
  have hEz : Subgroup.zpowers e = E :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr heE) (by rw [Nat.card_zpowers, hord, hE])
  have key : ∀ S : Subgroup (Fin 2 → Kˣ), Nat.card ↥S = 3 → e ∈ S → E = S := fun S hS heS =>
    Subgroup.eq_of_le_of_card_ge (hEz ▸ Subgroup.zpowers_le.mpr heS) (by rw [hS, hE])
  by_cases h0 : e 0 = 1
  · exact Or.inl (key _ (card_tSa.trans h3) (mem_tSa.mpr h0))
  by_cases h1 : e 1 = 1
  · exact Or.inr (Or.inl (key _ (card_tSb.trans h3) (mem_tSb.mpr h1)))
  rcases units_cases hK h0 (e 1) with h | h | h
  · exact absurd h h1
  · exact Or.inr (Or.inr (Or.inr (key _ (card_tSd.trans h3) (mem_tSd.mpr h.symm))))
  · exact Or.inr (Or.inr (Or.inl (key _ (card_tSc.trans h3)
      (mem_tSc.mpr (by rw [h, mul_inv_cancel])))))

omit [Finite K] in
theorem exists_units_ne_one (hK : Nat.card K = 4) : ∃ a : Kˣ, a ≠ 1 := by
  have h3 : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have : Finite Kˣ := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial Kˣ := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  exact exists_ne 1

omit [Finite K] in
theorem tS_pairwise_ne (hK : Nat.card K = 4) :
    tSa K ≠ tSb K ∧ tSa K ≠ tSc K ∧ tSa K ≠ tSd K ∧ tSb K ≠ tSc K ∧ tSb K ≠ tSd K ∧
      tSc K ≠ tSd K := by
  obtain ⟨a, ha⟩ := exists_units_ne_one hK
  have hai := inv_ne_self_units hK ha
  have m1 : (![1, a] : Fin 2 → Kˣ) ∈ tSa K := mem_tSa.mpr rfl
  have m2 : (![a, 1] : Fin 2 → Kˣ) ∈ tSb K := mem_tSb.mpr rfl
  have m3 : (![a, a⁻¹] : Fin 2 → Kˣ) ∈ tSc K := mem_tSc.mpr (mul_inv_cancel a)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h] at m1
    exact ha (mem_tSb.mp m1)
  · rw [h] at m1
    exact ha (by simpa using mem_tSc.mp m1)
  · rw [h] at m1
    exact ha (mem_tSd.mp m1).symm
  · rw [h] at m2
    exact ha (by simpa using mem_tSc.mp m2)
  · rw [h] at m2
    exact ha (mem_tSd.mp m2)
  · rw [h] at m3
    exact hai (mem_tSd.mp m3).symm

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
