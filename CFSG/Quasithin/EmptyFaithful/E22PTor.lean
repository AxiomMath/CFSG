module

public import CFSG.Quasithin.Background.E1Sec6

public section

namespace CFSG.Quasithin.E22L2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem e22ptor_mem_four {A : Subgroup H} (hAcard : Nat.card A = 4) {a b : H} (hb : b ∈ A)
    (ha : a ∈ A) (hb1 : b ≠ 1) (hab : a ∉ Subgroup.zpowers b) {y : H} (hy : y ∈ A) :
    y = 1 ∨ y = a ∨ y = b ∨ y = a * b := by
  classical
  by_contra hcon
  obtain ⟨h1, h2, h3, h4⟩ : y ≠ 1 ∧ y ≠ a ∧ y ≠ b ∧ y ≠ a * b := by
    simpa only [not_or] using hcon
  have ha1 : a ≠ 1 := fun h => hab (h ▸ Subgroup.one_mem _)
  have hab' : a ≠ b := fun h => hab (h ▸ Subgroup.mem_zpowers b)
  have hab1 : a * b ≠ 1 := fun h => hab (by
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers b))
  have habA : a * b ≠ a := fun h => hb1 (by simpa using h)
  have habB : a * b ≠ b := fun h => ha1 (by simpa using h)
  have hcard : ({1, a, b, a * b, y} : Finset H).card = 5 := by
    simp [Finset.card_insert_of_notMem, ha1.symm, hb1.symm, hab', hab1.symm, habA.symm,
      habB.symm, h1.symm, h2.symm, h3.symm, h4.symm]
  have hsub : (({1, a, b, a * b, y} : Finset H) : Set H) ⊆ (A : Set H) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact A.one_mem
    · exact ha
    · exact hb
    · exact A.mul_mem ha hb
    · exact hy
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard] at hle
  have hA : (A : Set H).ncard = 4 := by
    rw [← hAcard, ← Nat.card_coe_set_eq]
    rfl
  omega

omit [Finite H] in
theorem e22ptor_exists_sq {r k : ℕ} (hr : Odd r) {x : H} (hx : x ^ r ^ k = 1) :
    ∃ j : ℕ, (x ^ j) ^ 2 = x := by
  obtain ⟨m, hm⟩ := hr.pow (n := k)
  refine ⟨m + 1, ?_⟩
  rw [← pow_mul, show (m + 1) * 2 = r ^ k + 1 by omega, pow_succ, hx, one_mul]

omit [Finite H] in
theorem e22ptor_exists_torsion (r : ℕ) {U : Subgroup H}
    (hc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) :
    ∃ P : Subgroup H, ∀ x : H, x ∈ P ↔ x ∈ U ∧ ∃ k : ℕ, x ^ r ^ k = 1 := by
  refine ⟨{ carrier := {x | x ∈ U ∧ ∃ k : ℕ, x ^ r ^ k = 1}
            one_mem' := ⟨U.one_mem, 0, one_pow _⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro x y ⟨hxU, i, hi⟩ ⟨hyU, j, hj⟩
    refine ⟨U.mul_mem hxU hyU, i + j, ?_⟩
    have hxy : Commute x y := hc x hxU y hyU
    rw [hxy.mul_pow, pow_add, pow_mul, hi, one_pow, one_mul, mul_comm (r ^ i), pow_mul, hj,
      one_pow]
  · rintro x ⟨hxU, k, hk⟩
    exact ⟨U.inv_mem hxU, k, by rw [inv_pow, hk, inv_one]⟩

theorem isE_one_of_odd_torus {T A U : Subgroup H} (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A) (hAcard : Nat.card A = 4) {b a : H} (hb : b ∈ A) (ha : a ∈ A)
    (hb2 : orderOf b = 2) (hab : a ∉ Subgroup.zpowers b) (hU : IsCyclic ↥U)
    (hbU : ∀ u ∈ U, b * u = u * b) (haU : ∀ u ∈ U, a * u * a⁻¹ = u⁻¹)
    (hτ : tauOf ⊤ T A ≤ Subgroup.normalizer (U : Set H)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrU : r ∣ Nat.card U) :
    ∃ P₀ : Subgroup H, P₀ ≤ U ∧ P₀ ≠ ⊥ ∧ IsPGroup r P₀ ∧ IsE 1 ⊤ T A (P₀ ⊔ tauOf ⊤ T A) ∧
      ¬ P₀ ≤ Subgroup.centralizer ({a} : Set H) := by
  have hr' : Odd r := hr.odd_of_ne_two hr2
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb2; omega
  have hcU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy => setLike_mul_comm hx hy
  obtain ⟨P₀, hP₀⟩ := e22ptor_exists_torsion r hcU
  have hPU : P₀ ≤ U := fun x hx => ((hP₀ x).1 hx).1
  have hPgrp : IsPGroup r P₀ := fun x => by
    obtain ⟨k, hk⟩ := ((hP₀ x).1 x.2).2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hPne : P₀ ≠ ⊥ := by
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥U) r hrU
    have hxo : orderOf (x : H) = r := (Subgroup.orderOf_coe x).trans hx
    have hxP : (x : H) ∈ P₀ := (hP₀ _).2 ⟨x.2, 1, by rw [pow_one]; exact hxo ▸ pow_orderOf_eq_one _⟩
    have hx1 : (x : H) ≠ 1 := fun h => by
      rw [h, orderOf_one] at hxo
      exact hr.one_lt.ne hxo
    intro hbot
    exact hx1 (Subgroup.mem_bot.mp (hbot ▸ hxP))
  have hτP : tauOf ⊤ T A ≤ Subgroup.normalizer (P₀ : Set H) := by
    intro t ht
    apply mem_normalizer_of_conj_mem
    intro x hx
    obtain ⟨hxU, k, hk⟩ := (hP₀ x).1 hx
    refine (hP₀ _).2 ⟨(Subgroup.mem_normalizer_iff.mp (hτ ht) x).mp hxU, k, ?_⟩
    rw [conj_pow, hk]
    group
  have hAact : ∀ y ∈ A, ∀ u ∈ U, y * u * y⁻¹ = u ∨ y * u * y⁻¹ = u⁻¹ := by
    intro y hy u hu
    rcases e22ptor_mem_four hAcard hb ha hb1 hab hy with h | h | h | h
    · left
      rw [h]
      group
    · right
      rw [h]
      exact haU u hu
    · left
      rw [h, hbU u hu]
      group
    · right
      have : y * u * y⁻¹ = a * (b * u * b⁻¹) * a⁻¹ := by rw [h]; group
      rw [this, hbU u hu]
      simpa using haU u hu
  have hAnorm : A ≤ Subgroup.normalizer (P₀ : Set H) := by
    intro y hy
    apply mem_normalizer_of_conj_mem
    intro x hx
    rcases hAact y hy x ((hP₀ x).1 hx).1 with h | h
    · rw [h]
      exact hx
    · rw [h]
      exact P₀.inv_mem hx
  have hcomm : ⁅P₀, A⁆ = P₀ := by
    refine le_antisymm (commutator_le_of_le_normalizer hAnorm) fun x hx => ?_
    obtain ⟨hxU, k, hk⟩ := (hP₀ x).1 hx
    obtain ⟨j, hj⟩ := e22ptor_exists_sq hr' hk
    have hxj : x ^ j ∈ P₀ := P₀.pow_mem hx j
    have h1 : ⁅x ^ j, a⁆ = x := by
      have h2 := haU (x ^ j) (U.pow_mem hxU j)
      have h3 : ⁅x ^ j, a⁆ = x ^ j * (a * x ^ j * a⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [h3, h2, inv_inv, ← sq]
      exact hj
    rw [← h1]
    exact Subgroup.commutator_mem_commutator hxj ha
  have hBA : Subgroup.zpowers b ≤ A := Subgroup.zpowers_le.mpr hb
  have hBc : Subgroup.zpowers b ≤ Subgroup.centralizer (P₀ : Set H) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun x hx => (hbU x (hPU hx)).symm)
  have hBidx : (Subgroup.zpowers b).relIndex A ≤ 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.zpowers b) (K := A)
    rw [inf_eq_left.mpr hBA, Nat.card_zpowers, hb2, hAcard] at h1
    omega
  have hnc : ¬ P₀ ≤ Subgroup.centralizer ({a} : Set H) := by
    intro hle
    apply hPne
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨hxU, k, hk⟩ := (hP₀ x).1 hx
    obtain ⟨j, hj⟩ := e22ptor_exists_sq hr' hk
    have hax : a * x = x * a := (Subgroup.mem_centralizer_iff.mp (hle hx) a rfl)
    have hxx : x = x⁻¹ := by
      have h2 := haU x hxU
      rw [hax] at h2
      calc x = x * a * a⁻¹ := by group
        _ = x⁻¹ := h2
    have hsq : x ^ 2 = 1 := by
      rw [sq]
      calc x * x = x * x⁻¹ := by rw [← hxx]
        _ = 1 := mul_inv_cancel x
    rw [← hj, ← pow_mul, mul_comm, pow_mul, hsq, one_pow]
  exact ⟨P₀, hPU, hPne, hPgrp, (isE_one_sup hr hr2 hT hAT hA hPgrp hPne hτP hcomm hBA hBc hBidx).1,
    hnc⟩

end CFSG.Quasithin.E22L2
