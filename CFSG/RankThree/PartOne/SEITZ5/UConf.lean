module

public import CFSG.RankThree.PartOne.SEITZ5.UVec

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem exists_two_indices (hn : 4 ≤ n) (i j : Fin n) :
    ∃ l m : Fin n, l ≠ i ∧ l ≠ j ∧ m ≠ i ∧ m ≠ j ∧ l ≠ m := by
  classical
  set S : Finset (Fin n) := ((Finset.univ : Finset (Fin n)).erase i).erase j with hS
  have hcard : 2 ≤ S.card := by
    have h1 : n - 1 ≤ ((Finset.univ : Finset (Fin n)).erase i).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have h2 : ((Finset.univ : Finset (Fin n)).erase i).card - 1 ≤ S.card := by
      rw [hS]
      exact Finset.pred_card_le_card_erase
    omega
  obtain ⟨l, hl, m, hm, hlm⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
  simp only [hS, Finset.mem_erase, Finset.mem_univ, and_true] at hl hm
  exact ⟨l, m, hl.2, hl.1, hm.2, hm.1, hlm⟩

theorem config_vec2 [CharP K 2] {k : Subfield K} {p q p' q' : Fin n} (hpq : p ≠ q) (hpp : p ≠ p')
    (hpq' : p ≠ q') (hqp : q ≠ p') (hqq : q ≠ q') {a b ω : K} (hωk : ω ∈ k) (ha : a ∈ k)
    (hb : b ∈ k) (hω1 : ω ≠ 1) (hna : σ a * a = 1) (hnb : σ b * b = 1) (hωn : σ ω * ω = 1)
    (hp'q' : p' ≠ q') :
    IsRat k (vec2 p q 1 a) ∧ IsRat k (vec2 p' q' 1 b) ∧ IsRat k (vec2 p q 1 (a * ω)) ∧
      herm σ (vec2 p q 1 a) (vec2 p q 1 a) = 0 ∧ herm σ (vec2 p' q' 1 b) (vec2 p' q' 1 b) = 0 ∧
      herm σ (vec2 p q 1 (a * ω)) (vec2 p q 1 (a * ω)) = 0 ∧
      herm σ (vec2 p q 1 a) (vec2 p' q' 1 b) = 0 ∧
      herm σ (vec2 p' q' 1 b) (vec2 p q 1 (a * ω)) = 0 ∧
      herm σ (vec2 p q 1 a) (vec2 p q 1 (a * ω)) ≠ 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨isRat_vec2 p q k.one_mem ha, isRat_vec2 p' q' k.one_mem hb,
    isRat_vec2 p q k.one_mem (k.mul_mem ha hωk), ?_, ?_, ?_, herm_vec2_vec2_disj hpp hpq' hqp hqq
      _ _ _ _, ?_, ?_⟩
  · rw [herm_vec2_vec2_same hpq, map_one, hna]
    linear_combination h2
  · rw [herm_vec2_vec2_same hp'q', map_one, hnb]
    linear_combination h2
  · rw [herm_vec2_vec2_same hpq, map_one, map_mul, show σ a * σ ω * (a * ω) = (σ a * a) * (σ ω * ω)
      by ring, hna, hωn]
    linear_combination h2
  · rw [herm_vec2_vec2_disj (Ne.symm hpp) (Ne.symm hqp) (Ne.symm hpq') (Ne.symm hqq)]
  · rw [herm_vec2_vec2_same hpq, map_one, show σ a * (a * ω) = (σ a * a) * ω by ring, hna]
    intro h
    apply hω1
    linear_combination h - h2

theorem exists_a [CharP K 2] {k : Subfield K} {ω : K} (hωk : ω ∈ k) (hω1 : ω ≠ 1)
    (hω2 : ω ^ 2 + ω + 1 = 0) {yi yj β : K} (hi : yi ≠ 0) (hj : ∀ c ∈ k, yj ≠ c * yi)
    (hβ : β ≠ 0) :
    (yi + yj ≠ 0 ∧ yi + ω ^ 2 * yj ≠ 0) ∧
      (β / (yi + yj) ∉ k ∨ β / (yi + ω ^ 2 * yj) ∉ k) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω2
  have hω0 : ω ≠ 0 := fun h => by rw [h] at hω3; simp at hω3
  have h1 : yi + yj ≠ 0 := fun h => hj 1 k.one_mem (by linear_combination h - yi * h2)
  have h3 : yi + ω ^ 2 * yj ≠ 0 := fun h => hj ω hωk (by
    linear_combination (ω : K) * h - yj * hω3 - (ω * yi) * h2)
  refine ⟨⟨h1, h3⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hc1, hcω⟩ := hcon
  set c₁ : K := β / (yi + yj) with hc₁
  set cω : K := β / (yi + ω ^ 2 * yj) with hcω'
  have e1 : β = c₁ * (yi + yj) := by rw [hc₁]; field_simp
  have e2 : β = cω * (yi + ω ^ 2 * yj) := by rw [hcω']; field_simp
  by_cases hne : cω * ω ^ 2 - c₁ = 0
  · have h4 : c₁ = cω * ω ^ 2 := by linear_combination -hne
    have h5 : (c₁ - cω) * yi = 0 := by
      linear_combination e2 - e1 + yj * hne
    have h6 : c₁ = cω := by
      have := (mul_eq_zero.1 h5).resolve_right hi
      linear_combination this
    have hω2ne : ω ^ 2 - 1 ≠ 0 := by
      intro h
      apply hω1
      have : (ω - 1) ^ 2 = 0 := by linear_combination h + (1 - ω) * h2
      have := pow_eq_zero_iff (two_ne_zero) |>.1 this
      linear_combination this
    have hcω0 : cω = 0 := by
      have : cω * (ω ^ 2 - 1) = 0 := by linear_combination (-1 : K) * h4 + h6
      exact (mul_eq_zero.1 this).resolve_right hω2ne
    exact hβ (by rw [e2, hcω0, zero_mul])
  · refine hj ((c₁ - cω) / (cω * ω ^ 2 - c₁)) (k.div_mem (k.sub_mem hc1 hcω)
      (k.sub_mem (k.mul_mem hcω (k.pow_mem hωk 2)) hc1)) ?_
    field_simp
    linear_combination e1 - e2

theorem exists_config [CharP K 2] {k : Subfield K} {ω : K} (hωk : ω ∈ k) (hω1 : ω ≠ 1)
    (hω : σ ω = ω ^ 2) (hω2 : ω ^ 2 + ω + 1 = 0) (hωn : σ ω * ω = 1) (hn : 4 ≤ n)
    {y : Fin n → K} {i j : Fin n} (hi : y i ≠ 0) (hj : ∀ c ∈ k, y j ≠ c * y i) :
    ∃ e w f : Fin n → K, IsRat k e ∧ IsRat k w ∧ IsRat k f ∧ herm σ e e = 0 ∧
      herm σ w w = 0 ∧ herm σ f f = 0 ∧ herm σ e w = 0 ∧ herm σ w f = 0 ∧ herm σ e f ≠ 0 ∧
      herm σ e y ≠ 0 ∧ herm σ w y / herm σ e y ∉ k := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hij : i ≠ j := fun h => hj 1 k.one_mem (by rw [← h, one_mul])
  obtain ⟨l, m, hli, hlj, hmi, hmj, hlm⟩ := exists_two_indices hn i j
  have h1n : σ (1 : K) * 1 = 1 := by simp
  by_cases hlm0 : y l = 0 ∧ y m = 0
  · obtain ⟨hyl, hym⟩ := hlm0
    obtain ⟨hr1, hr2, hr3, hee, hww, hff, hew, hwf, hef⟩ := config_vec2 (σ := σ) (k := k)
      (p := i) (q := l) (p' := j) (q' := m) hli.symm hij hmi.symm hlj hlm hωk k.one_mem
      k.one_mem hω1 h1n h1n hωn hmj.symm
    refine ⟨vec2 i l 1 1, vec2 j m 1 1, vec2 i l 1 (1 * ω), hr1, hr2, hr3, hee, hww, hff, hew,
      hwf, hef, ?_, ?_⟩
    · rw [herm_vec2_left, hyl, map_one, one_mul, mul_zero, add_zero]
      exact hi
    · simp only [herm_vec2_left, hyl, hym, map_one, one_mul, mul_zero, add_zero]
      intro hc
      exact hj _ hc (by field_simp)
  · have hlm1 : y l ≠ 0 ∨ y m ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hlm0 hcon
    obtain ⟨b, hbk, hnb, hβ₂⟩ : ∃ b : K, b ∈ k ∧ σ b * b = 1 ∧ y l + σ b * y m ≠ 0 := by
      by_cases h : y l + y m = 0
      · have hyl : y l ≠ 0 := by
          intro hl0
          rcases hlm1 with h' | h'
          · exact h' hl0
          · apply h'
            linear_combination h - hl0
        refine ⟨ω, hωk, hωn, ?_⟩
        rw [hω]
        intro h'
        apply hyl
        have hym : y m = y l := by linear_combination h - y l * h2
        have h3 : y l * ω = 0 := by rw [hym] at h'; linear_combination (-1 : K) * h' + (y l) * hω2
        have hω0 : ω ≠ 0 := fun h0 => by
          have : σ ω * ω = 1 := hωn
          rw [h0] at this
          simp at this
        exact (mul_eq_zero.1 h3).resolve_right hω0
      · exact ⟨1, k.one_mem, h1n, by simpa using h⟩
    obtain ⟨⟨hA1, hAω⟩, hcase⟩ := exists_a hωk hω1 hω2 hi hj hβ₂
    obtain ⟨a, hak, hna, hβ₁, hρ⟩ : ∃ a : K, a ∈ k ∧ σ a * a = 1 ∧ y i + σ a * y j ≠ 0 ∧
        (y l + σ b * y m) / (y i + σ a * y j) ∉ k := by
      rcases hcase with hc | hc
      · exact ⟨1, k.one_mem, h1n, by simpa using hA1, by simpa using hc⟩
      · exact ⟨ω, hωk, hωn, by rw [hω]; exact hAω, by rw [hω]; exact hc⟩
    obtain ⟨hr1, hr2, hr3, hee, hww, hff, hew, hwf, hef⟩ := config_vec2 (σ := σ) (k := k)
      (p := i) (q := j) (p' := l) (q' := m) hij hli.symm hmi.symm hlj.symm hmj.symm hωk hak hbk
      hω1 hna hnb hωn hlm
    refine ⟨vec2 i j 1 a, vec2 l m 1 b, vec2 i j 1 (a * ω), hr1, hr2, hr3, hee, hww, hff, hew,
      hwf, hef, ?_, ?_⟩
    · rw [herm_vec2_left, map_one, one_mul]
      exact hβ₁
    · simp only [herm_vec2_left, map_one, one_mul]
      exact hρ

end CFSG.RankThree.PartOne.SEITZ5
