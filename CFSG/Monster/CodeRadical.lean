module

public import CFSG.Monster.Code.Weights

public section

namespace CFSG.Monster.Code

open Finset

private theorem zmod2_cases' (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact .inl rfl
  · exact .inr rfl

private theorem hammingNorm_eq_card (x : Fin 24 → ZMod 2) :
    hammingNorm x = #(univ.filter fun i => x i ≠ 0) := rfl

private theorem filter_mul_subset (a d : Fin 24 → ZMod 2) :
    (univ.filter fun i => (a * d) i ≠ 0) ⊆ univ.filter fun i => d i ≠ 0 := by
  intro i
  simp only [mem_filter, mem_univ, true_and, Pi.mul_apply]
  intro h hd
  exact h (by rw [hd, mul_zero])

private theorem hammingNorm_add_of_subset {d e : Fin 24 → ZMod 2}
    (h : (univ.filter fun i => e i ≠ 0) ⊆ univ.filter fun i => d i ≠ 0) :
    hammingNorm (d + e) = hammingNorm d - hammingNorm e := by
  rw [hammingNorm_eq_card, hammingNorm_eq_card, hammingNorm_eq_card, ← card_sdiff_of_subset h]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, mem_sdiff, Pi.add_apply]
  have hi : e i ≠ 0 → d i ≠ 0 := fun h' => (mem_filter.1 (h (mem_filter.2 ⟨mem_univ i, h'⟩))).2
  revert hi
  rcases zmod2_cases' (d i) with hd | hd <;> rcases zmod2_cases' (e i) with he | he <;>
    rw [hd, he] <;> decide

private theorem eq_of_subset_of_hammingNorm_eq {d e : Fin 24 → ZMod 2}
    (h : (univ.filter fun i => e i ≠ 0) ⊆ univ.filter fun i => d i ≠ 0)
    (hc : hammingNorm e = hammingNorm d) : e = d := by
  have heq := eq_of_subset_of_card_le h (by rw [← hammingNorm_eq_card, ← hammingNorm_eq_card, hc])
  funext i
  have := congrArg (i ∈ ·) heq
  simp only [mem_filter, mem_univ, true_and, eq_iff_iff] at this
  revert this
  rcases zmod2_cases' (d i) with hd | hd <;> rcases zmod2_cases' (e i) with he | he <;>
    rw [hd, he] <;> decide

private theorem hammingNorm_add_Ω (d : Fin 24 → ZMod 2) :
    hammingNorm (d + Ω) = 24 - hammingNorm d := by
  have hpt : ∀ i, (d + Ω) i ≠ 0 ↔ ¬ d i ≠ 0 := by
    intro i
    simp only [Pi.add_apply, Ω]
    rcases zmod2_cases' (d i) with hd | hd <;> rw [hd] <;> decide
  have h : (univ.filter fun i => (d + Ω) i ≠ 0) = univ \ univ.filter fun i => d i ≠ 0 := by
    ext i
    rw [mem_filter, mem_sdiff, mem_filter, hpt i]
    simp
  rw [hammingNorm_eq_card, h, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
    ← hammingNorm_eq_card]

private theorem const_on_supp {d : Fin 24 → ZMod 2} (hd : d ∈ C)
    (hP : ∀ a ∈ C, a * d ∈ C) (hw : hammingNorm d = 8 ∨ hammingNorm d = 12) {a : Fin 24 → ZMod 2}
    (ha : a ∈ C) {i j : Fin 24} (hi : d i ≠ 0) (hj : d j ≠ 0) : a i = a j := by
  have had := hP a ha
  have hsub := filter_mul_subset a d
  have hle : hammingNorm (a * d) ≤ hammingNorm d := card_le_card hsub
  have hmem := wt_mem had
  have hd1 : ∀ k, d k ≠ 0 → d k = 1 := fun k hk => (zmod2_cases' (d k)).resolve_left hk
  have hcases : a * d = 0 ∨ a * d = d := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h0 | h8 | h12 | h16 | h24
    · exact .inl (hammingNorm_eq_zero.1 h0)
    · rcases hw with hw | hw
      · exact .inr (eq_of_subset_of_hammingNorm_eq hsub (by omega))
      ·
        exfalso
        have hsum := C.add_mem hd had
        have h4 := hammingNorm_add_of_subset hsub
        have := wt_mem hsum
        rw [h4, h8, hw] at this
        simp at this
    · exact .inr (eq_of_subset_of_hammingNorm_eq hsub (by omega))
    · omega
    · omega
  rcases hcases with h | h
  · have hai : a i = 0 := by
      have := congrFun h i
      simp only [Pi.mul_apply, Pi.zero_apply, hd1 i hi, mul_one] at this
      exact this
    have haj : a j = 0 := by
      have := congrFun h j
      simp only [Pi.mul_apply, Pi.zero_apply, hd1 j hj, mul_one] at this
      exact this
    rw [hai, haj]
  · have hai : a i = 1 := by
      have := congrFun h i
      simp only [Pi.mul_apply, hd1 i hi, mul_one] at this
      exact this
    have haj : a j = 1 := by
      have := congrFun h j
      simp only [Pi.mul_apply, hd1 j hj, mul_one] at this
      exact this
    rw [hai, haj]

theorem mul_mem_C_iff {d : Fin 24 → ZMod 2} (hd : d ∈ C) :
    (∀ a ∈ C, a * d ∈ C) ↔ d = 0 ∨ d = Ω := by
  constructor
  · intro hP
    by_contra hne
    push Not at hne
    obtain ⟨d', hd', hP', hw', hsupp⟩ : ∃ d', d' ∈ C ∧ (∀ a ∈ C, a * d' ∈ C) ∧
        (hammingNorm d' = 8 ∨ hammingNorm d' = 12) ∧ 2 ≤ hammingNorm d' := by
      have hmem := wt_mem hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      have hPΩ : ∀ a ∈ C, a * (d + Ω) ∈ C := fun a ha => by
        rw [mul_add, show a * Ω = a by funext i; simp [Ω]]
        exact C.add_mem (hP a ha) ha
      rcases hmem with h0 | h8 | h12 | h16 | h24
      · exact absurd (hammingNorm_eq_zero.1 h0) hne.1
      · exact ⟨d, hd, hP, .inl h8, by omega⟩
      · exact ⟨d, hd, hP, .inr h12, by omega⟩
      · refine ⟨d + Ω, C.add_mem hd Ω_mem_C, hPΩ, .inl ?_, ?_⟩
        · rw [hammingNorm_add_Ω, h16]
        · rw [hammingNorm_add_Ω, h16]
          norm_num
      · exfalso
        apply hne.2
        have h := hammingNorm_add_Ω d
        rw [h24] at h
        have h0 : d + Ω = 0 := hammingNorm_eq_zero.1 h
        funext i
        have := congrFun h0 i
        simp only [Pi.add_apply, Pi.zero_apply, Ω] at this ⊢
        rcases zmod2_cases' (d i) with hdi | hdi
        · rw [hdi] at this; exact absurd this (by decide)
        · exact hdi
    obtain ⟨i, hi, j, hj, hij⟩ : ∃ i, d' i ≠ 0 ∧ ∃ j, d' j ≠ 0 ∧ i ≠ j := by
      have h1 : 1 < #(univ.filter fun k => d' k ≠ 0) := by
        rw [← hammingNorm_eq_card]; omega
      obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.1 h1
      exact ⟨i, (mem_filter.1 hi).2, j, (mem_filter.1 hj).2, hij⟩
    set e : Fin 24 → ZMod 2 := Pi.single i 1 + Pi.single j 1 with he
    have heC : e ∈ C := by
      rw [mem_C_iff_forall_dotProduct]
      intro a ha
      rw [dotProduct_comm, he, dotProduct_add, dotProduct_single, dotProduct_single, mul_one,
        mul_one, const_on_supp hd' hP' hw' ha hi hj]
      rcases zmod2_cases' (a j) with h | h <;> rw [h] <;> decide
    have hwe : hammingNorm e = 2 := by
      have : (univ.filter fun k => e k ≠ 0) = {i, j} := by
        ext k
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, he, Pi.add_apply]
        by_cases hki : k = i
        · subst hki
          simp [hij]
        · by_cases hkj : k = j
          · subst hkj
            simp [hki]
          · simp [hki, hkj]
      rw [hammingNorm_eq_card, this, card_pair hij]
    have hne0 : e ≠ 0 := by
      intro h0
      rw [h0, hammingNorm_zero] at hwe
      exact absurd hwe (by decide)
    have := eight_le_wt heC hne0
    omega
  · rintro (rfl | rfl)
    · intro a _
      rw [mul_zero]
      exact C.zero_mem
    · intro a ha
      rwa [show a * Ω = a by funext i; simp [Ω]]

end CFSG.Monster.Code
