module

public import CFSG.YGroups.Y433.Y322Embed

public section

namespace CFSG.YGroups

open CFSG.Certificates.CosetEnumeration (evalWord)

theorem commute_F433_231_of_D1_E1 {c : ℕ} (hc : c = 3 ∨ c = 4) :
    Commute (yGen 4 3 3 c) (F433 2 3 1) := by
  have key : ∀ s ∈ [3, 4], ∀ l ∈ [0, 5, 6, 7, 8, 9, 1],
      l < ngen 4 3 3 ∧ l ≠ s ∧ (s, l) ∉ yEdges 4 3 3 ∧ (l, s) ∉ yEdges 4 3 3 := by decide
  have hs : c ∈ [3, 4] := by simpa using hc
  rw [F433_eq_evalWord]
  exact (Relabel.commute_yGen_evalWord (by rcases hc with rfl | rfl <;> decide)
    (key c hs)).pow_right 9

theorem commute_F433_213_D3 : Commute (yGen 4 3 3 10) (F433 2 1 3) := by
  have key : ∀ l ∈ [0, 5, 6, 7, 1, 2, 8],
      l < ngen 4 3 3 ∧ l ≠ 10 ∧ (10, l) ∉ yEdges 4 3 3 ∧ (l, 10) ∉ yEdges 4 3 3 := by decide
  rw [F433_eq_evalWord]
  exact (Relabel.commute_yGen_evalWord (by decide) key).pow_right 9

theorem yGen_mul_F433_213
    {c : ℕ} (hc : c < ngen 4 3 3) :
    yGen 4 3 3 c * F433 2 1 3 = F433 2 1 3 * yGen 4 3 3 c := by
  by_cases h34 : c = 3 ∨ c = 4
  · rw [← F433_231_eq_213]
    exact (commute_F433_231_of_D1_E1 h34).eq
  by_cases h10 : c = 10
  · subst h10
    exact commute_F433_213_D3.eq
  · have hex : ∃ j, j < 8 ∧ U433.sub231 j = c := by
      have : ∀ c < ngen 4 3 3, ¬ (c = 3 ∨ c = 4) → c ≠ 10 → ∃ j, j < 8 ∧ U433.sub231 j = c := by
        decide
      exact this c hc h34 h10
    obtain ⟨j, hj, rfl⟩ := hex
    rw [← F433_231_eq_213]
    exact F433_231_comm_sub231 hj

theorem F433_213_mem_center :
    F433 2 1 3 ∈ Subgroup.center U433 :=
  Relabel.mem_center_of_commute_yGen fun _ hc => yGen_mul_F433_213 hc

theorem F433_213_mul_self :
    F433 2 1 3 * F433 2 1 3 = 1 := by
  rw [← F433_231_eq_213]
  exact F433_231_mul_self

theorem commute_F433_321_of_D1_E1 {c : ℕ} (hc : c = 3 ∨ c = 4) :
    Commute (yGen 4 3 3 c) (F433 3 2 1) := by
  have key : ∀ s ∈ [3, 4], ∀ l ∈ [0, 8, 9, 10, 5, 6, 1],
      l < ngen 4 3 3 ∧ l ≠ s ∧ (s, l) ∉ yEdges 4 3 3 ∧ (l, s) ∉ yEdges 4 3 3 := by decide
  have hs : c ∈ [3, 4] := by simpa using hc
  rw [F433_eq_evalWord]
  exact (Relabel.commute_yGen_evalWord (by rcases hc with rfl | rfl <;> decide)
    (key c hs)).pow_right 9

theorem commute_F433_312_D2 : Commute (yGen 4 3 3 7) (F433 3 1 2) := by
  have key : ∀ l ∈ [0, 8, 9, 10, 1, 2, 5],
      l < ngen 4 3 3 ∧ l ≠ 7 ∧ (7, l) ∉ yEdges 4 3 3 ∧ (l, 7) ∉ yEdges 4 3 3 := by decide
  rw [F433_eq_evalWord]
  exact (Relabel.commute_yGen_evalWord (by decide) key).pow_right 9

theorem yGen_mul_F433_312
    {c : ℕ} (hc : c < ngen 4 3 3) :
    yGen 4 3 3 c * F433 3 1 2 = F433 3 1 2 * yGen 4 3 3 c := by
  by_cases h34 : c = 3 ∨ c = 4
  · rw [← F433_321_eq_312]
    exact (commute_F433_321_of_D1_E1 h34).eq
  by_cases h7 : c = 7
  · subst h7
    exact commute_F433_312_D2.eq
  · have hex : ∃ j, j < 8 ∧ U433.sub312 j = c := by
      have : ∀ c < ngen 4 3 3, ¬ (c = 3 ∨ c = 4) → c ≠ 7 → ∃ j, j < 8 ∧ U433.sub312 j = c := by
        decide
      exact this c hc h34 h7
    obtain ⟨j, hj, rfl⟩ := hex
    exact F433_312_comm_sub312 hj

theorem F433_312_mem_center :
    F433 3 1 2 ∈ Subgroup.center U433 :=
  Relabel.mem_center_of_commute_yGen fun _ hc => yGen_mul_F433_312 hc

namespace U433

theorem relators_even : ∀ w ∈ yRels 4 3 3, w.length % 2 = 0 := by decide +kernel

noncomputable def sgn : U433 →* Multiplicative (ZMod 2) :=
  yModelHom (fun _ => Multiplicative.ofAdd (1 : ZMod 2)) (by
    intro w hw
    rw [evalWord_const_ofAdd]
    have h0 : ((w.length : ℕ) : ZMod 2) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_of_mod_eq_zero (relators_even w hw)
    rw [h0]
    rfl)

theorem sgn_yGen {c : ℕ} (hc : c < ngen 4 3 3) : sgn (yGen 4 3 3 c) = Multiplicative.ofAdd 1 :=
  yModelHom_yGen hc

theorem armStart_le (i : ℕ) : armStart i ≤ 8 := by
  unfold armStart
  split <;> omega

theorem sgn_F433 (i j k : ℕ) : sgn (F433 i j k) = Multiplicative.ofAdd 1 := by
  have h0 : sgn A = Multiplicative.ofAdd 1 := sgn_yGen (by decide)
  have hB : ∀ i, sgn (B i) = Multiplicative.ofAdd 1 := fun i =>
    sgn_yGen (by have := armStart_le i; unfold ngen; omega)
  have hC : ∀ i, sgn (C i) = Multiplicative.ofAdd 1 := fun i =>
    sgn_yGen (by have := armStart_le i; unfold ngen; omega)
  have hD : ∀ i, sgn (D i) = Multiplicative.ofAdd 1 := fun i =>
    sgn_yGen (by have := armStart_le i; unfold ngen; omega)
  simp only [F433, map_pow, map_mul, h0, hB, hC, hD]
  decide

end U433

theorem F433_ne_one (i j k : ℕ) : F433 i j k ≠ 1 := by
  intro h
  have := U433.sgn_F433 i j k
  rw [h, map_one] at this
  exact absurd (Multiplicative.ofAdd.injective this) (by decide)

theorem orderOf_F433_213 :
    orderOf (F433 2 1 3) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact F433_213_mul_self) (F433_ne_one 2 1 3)

theorem orderOf_F433_312 :
    orderOf (F433 3 1 2) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact F433_312_mul_self) (F433_ne_one 3 1 2)

namespace R433

theorem π_F433_231 :
    π (F433 2 3 1) = 1 := by
  rw [F433_231_eq_213]
  exact π_F433_213

theorem π_mem_center {x : U433} (hx : x ∈ Subgroup.center U433) : π x ∈ Subgroup.center R433 := by
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro g
  obtain ⟨u, rfl⟩ := π_surjective g
  rw [← map_mul, ← map_mul, hx u]

theorem π_F433_312_mem_center :
    π (F433 3 1 2) ∈ Subgroup.center R433 :=
  π_mem_center F433_312_mem_center

theorem π_F433_312_mul_self :
    π (F433 3 1 2) * π (F433 3 1 2) = 1 := by
  rw [← map_mul, F433_312_mul_self, map_one]

end R433

end CFSG.YGroups
