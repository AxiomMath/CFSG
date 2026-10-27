module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.LieType.SpecialLinear.ExteriorModel

private theorem c2slr5_eq_zero_of_shift_one {n f : ℕ} (hf : 0 < f)
    (ε : Fin f → Finset (Fin n))
    (hrot : ∀ r : Fin f, ε ⟨(r + 1) % f, Nat.mod_lt _ r.pos⟩ = ε r) :
    ∀ r : Fin f, ε r = ε ⟨0, hf⟩ := by
  have hiter : ∀ k : ℕ, ε ⟨k % f, Nat.mod_lt k hf⟩ = ε ⟨0, hf⟩ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hk : k % f < f := Nat.mod_lt k hf
        have hstep := hrot ⟨k % f, hk⟩
        have hmod : (k % f + 1) % f = (k + 1) % f := by
          have h1 : (k + 1) % f = (k % f + 1 % f) % f := Nat.add_mod k 1 f
          have h2 : (k % f + 1) % f = (k % f + 1 % f) % f := by
            simpa using Nat.add_mod (k % f) 1 f
          rw [h2, h1]
        have heqfin : (⟨(k % f + 1) % f, Nat.mod_lt _ (⟨k % f, hk⟩ : Fin f).pos⟩ : Fin f) =
            ⟨(k + 1) % f, Nat.mod_lt (k + 1) hf⟩ := Fin.ext hmod
        rw [heqfin] at hstep
        exact hstep.trans ih
  intro r
  have hfin : (⟨(r : ℕ) % f, Nat.mod_lt (r : ℕ) hf⟩ : Fin f) = r :=
    Fin.ext (Nat.mod_eq_of_lt r.isLt)
  have := hiter (r : ℕ)
  rwa [hfin] at this

private theorem c2slr5_card_two_le_orbitSize {n : ℕ} {S : Finset (Fin n)} (hn : 2 ≤ n)
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) (hcard : 2 ≤ S.card) :
    n * (n - 1) ≤ orbitSize S := by
  have hn0 : 0 < n := by omega
  rw [orbitSize, card_rearr_topWt]
  have hb : ∀ i, 0 < blocks S i := fun i => blocks_pos hn0 (by simpa using h0) i
  have hsum := sum_blocks S
  have hl : 3 ≤ S.card + 1 := by omega
  exact multinomial_lower (b := blocks S) hb hsum hl

private theorem c2slr5_single_of_orbitSize_le {n : ℕ} (hn : 2 ≤ n) {S : Finset (Fin n)}
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) (hne : S ≠ ∅) (hcard : orbitSize S ≤ n) :
    ∃ j : Fin n, S = {j} := by
  have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  by_cases h2 : 2 ≤ S.card
  · have hlow := c2slr5_card_two_le_orbitSize hn h0 h2
    have hc : S.card < n := by
      have := Finset.card_lt_univ_of_notMem h0
      rwa [Fintype.card_fin] at this
    have h4 : 2 ≤ n - 1 := by omega
    have hle : n * 2 ≤ n * (n - 1) := Nat.mul_le_mul_left n h4
    omega
  · have hcard1 : S.card = 1 := by omega
    exact Finset.card_eq_one.mp hcard1

private theorem c2slr5_single_of_orbitSize_le_three {n : ℕ} (hn : 5 ≤ n)
    {S : Finset (Fin n)} (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) (hne : S ≠ ∅)
    (hcard : orbitSize S ≤ 3 * n) : ∃ j : Fin n, S = {j} := by
  have hn2 : 2 ≤ n := by omega
  have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  by_cases h2 : 2 ≤ S.card
  · have hlow := c2slr5_card_two_le_orbitSize hn2 h0 h2
    have h4 : 4 ≤ n - 1 := by omega
    have hle : n * 4 ≤ n * (n - 1) := Nat.mul_le_mul_left n h4
    omega
  · have hcard1 : S.card = 1 := by omega
    exact Finset.card_eq_one.mp hcard1

private theorem c2slr5_succ_le_choose_two {n : ℕ} (hn : 4 ≤ n) : n + 1 ≤ n.choose 2 := by
  rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  have hquad : 3 * n + 2 ≤ n * n := by nlinarith
  have hgt : n ≤ n * n := by nlinarith
  have hsub : n * (n - 1) = n * n - n := by rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [hsub, show (n + 1) * 2 = 2 * n + 2 by ring]
  exact (Nat.le_sub_iff_add_le hgt).mpr (by omega)

private theorem c2slr5_choose_small {n j : ℕ} (hn : 5 ≤ n) (hn7 : n ≤ 7)
    (hj2 : 2 ≤ j) (hjn2 : j ≤ n - 2) (hC : n.choose j ≤ 3 * n) :
    (n = 5 ∧ (j = 2 ∨ j = 3)) ∨ (n = 6 ∧ (j = 2 ∨ j = 4)) ∨
      (n = 7 ∧ (j = 2 ∨ j = 5)) := by
  have hn567 : n = 5 ∨ n = 6 ∨ n = 7 := by omega
  rcases hn567 with rfl | rfl | rfl
  · have hj : j = 2 ∨ j = 3 := by omega
    rcases hj with rfl | rfl <;> decide
  · have hj : j = 2 ∨ j = 3 ∨ j = 4 := by omega
    rcases hj with rfl | rfl | rfl
    · decide
    · have h : Nat.choose 6 3 = 20 := by decide
      rw [h] at hC
      omega
    · decide
  · have hj : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases hj with rfl | rfl | rfl | rfl
    · decide
    · have h : Nat.choose 7 3 = 35 := by decide
      rw [h] at hC
      omega
    · have h : Nat.choose 7 4 = 35 := by decide
      rw [h] at hC
      omega
    · decide

private theorem c2slr5_s_eq_f_of_unique_active {n f s : ℕ} (hs : 1 ≤ s)
    (ε : Fin f → Finset (Fin n))
    (hmin : ∀ p : ℕ, 0 < p → p < s → ∃ r : Fin f,
      ε ⟨(r + p) % f, Nat.mod_lt _ r.pos⟩ ≠ ε r)
    (hper : f ≤ s * (univ.filter fun r => ε r ≠ ∅).card)
    (hcard : (univ.filter fun r => ε r ≠ ∅).card = 1) : s = f := by
  have hf1 : 1 ≤ f := by
    have hle : (univ.filter fun r => ε r ≠ ∅).card ≤ (univ : Finset (Fin f)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [hcard, Finset.card_univ, Fintype.card_fin] at hle
    omega
  have hfle : f ≤ s := by
    have := hper
    rw [hcard, mul_one] at this
    exact this
  have hnot : ¬ f < s := by
    intro hfs
    obtain ⟨r, hr⟩ := hmin f (by omega) hfs
    have heq : (⟨(r + f) % f, Nat.mod_lt _ r.pos⟩ : Fin f) = r := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt r.isLt]
    rw [heq] at hr
    exact hr rfl
  omega

theorem w135c2_psl_range_ge5 {n f s d : ℕ} (hn : 5 ≤ n)
    (hs : 1 ≤ s) (ε : Fin f → Finset (Fin n))
    (h0 : ∀ r, (⟨0, by omega⟩ : Fin n) ∉ ε r) (hact : ∃ r, ε r ≠ ∅)
    (hper : f ≤ s * (univ.filter fun r => ε r ≠ ∅).card)
    (hrot : ∀ r : Fin f, ε ⟨(r + s) % f, Nat.mod_lt _ r.pos⟩ = ε r)
    (hmin : ∀ p : ℕ, 0 < p → p < s → ∃ r : Fin f, ε ⟨(r + p) % f, Nat.mod_lt _ r.pos⟩ ≠ ε r)
    (hlow : ∏ r ∈ univ.filter (fun r => ε r ≠ ∅), orbitSize (ε r) ≤ d)
    (hrange : (s = 1 ∧ d ≤ 3 * n) ∨ ((s = 2 ∨ s = 3) ∧ d ≤ n)) :
    (∃ (r₀ : Fin f) (j : Fin n), (∀ r, r ≠ r₀ → ε r = ∅) ∧ ε r₀ = {j} ∧
        ((j : ℕ) = 1 ∨ (j : ℕ) + 1 = n) ∧ s = f ∧ s ≤ 3) ∨
      (f = 1 ∧ s = 1 ∧ ∃ j : Fin n, (∀ r, ε r = {j}) ∧
        ((n = 5 ∧ ((j : ℕ) = 2 ∨ (j : ℕ) = 3)) ∨ (n = 6 ∧ ((j : ℕ) = 2 ∨ (j : ℕ) = 4)) ∨
          (n = 7 ∧ ((j : ℕ) = 2 ∨ (j : ℕ) = 5)))) := by
  classical
  obtain ⟨r₀, hr₀⟩ := hact
  have hfpos : 0 < f := r₀.pos
  have hn2 : 2 ≤ n := by omega
  rcases hrange with ⟨hs1, hd3n⟩ | ⟨hs23, hdn⟩
  ·
    have hrot1 : ∀ r : Fin f, ε ⟨(r + 1) % f, Nat.mod_lt _ r.pos⟩ = ε r := by
      intro r
      simpa [hs1] using hrot r
    have hconst := c2slr5_eq_zero_of_shift_one hfpos ε hrot1
    have hSne : ε ⟨0, hfpos⟩ ≠ ∅ := by
      have := hr₀
      rw [hconst r₀] at this
      exact this
    have hfilter : (univ.filter fun r => ε r ≠ ∅) = univ := by
      apply Finset.filter_eq_self.mpr
      intro r _
      rw [hconst r]
      exact hSne
    have hprod : ∏ r ∈ univ.filter (fun r => ε r ≠ ∅), orbitSize (ε r) =
        orbitSize (ε ⟨0, hfpos⟩) ^ f := by
      rw [hfilter]
      simp only [hconst, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hNpow : orbitSize (ε ⟨0, hfpos⟩) ^ f ≤ 3 * n := by
      have := hlow
      rw [hprod] at this
      exact le_trans this hd3n
    have hNge : n ≤ orbitSize (ε ⟨0, hfpos⟩) :=
      n_le_orbitSize hn2 (h0 ⟨0, hfpos⟩) hSne
    have hf1 : f = 1 := by
      have hnpow : n ^ f ≤ 3 * n := le_trans (Nat.pow_le_pow_left hNge f) hNpow
      have hfle : f ≤ 1 := by
        by_contra hflt
        have hf2 : 2 ≤ f := by omega
        have hpow2 : n ^ 2 ≤ n ^ f := Nat.pow_le_pow_right (by omega : 0 < n) hf2
        have : n ^ 2 ≤ 3 * n := le_trans hpow2 hnpow
        nlinarith [hn]
      omega
    have hNs : orbitSize (ε ⟨0, hfpos⟩) ≤ 3 * n := by
      have hposo : 0 < orbitSize (ε ⟨0, hfpos⟩) :=
        lt_of_lt_of_le (by omega : 0 < n) hNge
      have hle : orbitSize (ε ⟨0, hfpos⟩) ≤ orbitSize (ε ⟨0, hfpos⟩) ^ f := by
        have h := Nat.pow_le_pow_right hposo (by omega : 1 ≤ f)
        rwa [pow_one] at h
      exact le_trans hle hNpow
    obtain ⟨j, hSj⟩ := c2slr5_single_of_orbitSize_le_three hn (h0 ⟨0, hfpos⟩) hSne hNs
    have hj_ne0 : (j : ℕ) ≠ 0 := by
      intro hj0
      have hj_eq : j = (⟨0, by omega⟩ : Fin n) := Fin.ext hj0
      exact h0 ⟨0, hfpos⟩ (by rw [hSj, hj_eq]; exact Finset.mem_singleton_self _)
    have hC : n.choose j ≤ 3 * n := by
      have := hNs
      rw [hSj, orbitSize_singleton] at this
      exact this
    by_cases hnat : (j : ℕ) = 1 ∨ (j : ℕ) + 1 = n
    · refine Or.inl ⟨⟨0, hfpos⟩, j, ?_, hSj, hnat, ?_, ?_⟩
      · intro r hr
        exact absurd (Fin.ext (by have := r.isLt; omega)) hr
      · omega
      · omega
    · obtain ⟨hj1, hjn⟩ := not_or.mp hnat
      have hj2 : 2 ≤ (j : ℕ) := by have := j.isLt; omega
      have hjn2 : (j : ℕ) ≤ n - 2 := by have := j.isLt; omega
      have h2le : n.choose 2 ≤ 3 * n := le_trans (choose_two_le_choose hj2 hjn2) hC
      have hnle7 : n ≤ 7 := by
        by_contra hle
        have hn8 : 8 ≤ n := by omega
        rw [Nat.choose_two_right] at h2le
        rw [Nat.div_le_iff_le_mul_add_pred (by norm_num : 0 < 2)] at h2le
        have h8 : 8 * (n - 1) ≤ n * (n - 1) := Nat.mul_le_mul_right (n - 1) hn8
        have hgt : 6 * n + 1 < 8 * (n - 1) := by omega
        omega
      have hdisj := c2slr5_choose_small hn hnle7 hj2 hjn2 hC
      refine Or.inr ⟨hf1, hs1, j, ?_, hdisj⟩
      · intro r
        have hr0 : r = ⟨0, hfpos⟩ := Fin.ext (by have := r.isLt; omega)
        rw [hr0]
        exact hSj
  ·
    set T : Finset (Fin f) := univ.filter (fun r => ε r ≠ ∅) with hT
    have hlowT : ∏ r ∈ T, orbitSize (ε r) ≤ d := by rw [hT]; exact hlow
    have hmem_prod : ∀ r ∈ T, n ≤ orbitSize (ε r) := by
      intro r hr
      rw [hT] at hr
      exact n_le_orbitSize hn2 (h0 r) (Finset.mem_filter.mp hr).2
    have hprod_ge : n ^ T.card ≤ ∏ r ∈ T, orbitSize (ε r) := by
      calc n ^ T.card = ∏ r ∈ T, n := (Finset.prod_const (s := T) n).symm
        _ ≤ ∏ r ∈ T, orbitSize (ε r) := Finset.prod_le_prod hmem_prod
    have hcardT : T.card = 1 := by
      by_contra hne
      have hrT : r₀ ∈ T := by
        rw [hT]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ r₀, hr₀⟩
      have hpos : 0 < T.card := Finset.card_pos.mpr ⟨r₀, hrT⟩
      have h2 : 2 ≤ T.card := by omega
      have hle : n ^ 2 ≤ ∏ r ∈ T, orbitSize (ε r) :=
        le_trans (Nat.pow_le_pow_right (by omega : 0 < n) h2) hprod_ge
      have : n ^ 2 ≤ n := le_trans hle (le_trans hlowT hdn)
      nlinarith [hn2]
    obtain ⟨r₁, hT1⟩ := Finset.card_eq_one.mp hcardT
    have huniq : ∀ r, r ≠ r₁ → ε r = ∅ := by
      intro r hr
      by_contra hne
      have hmem : r ∈ T := by
        rw [hT]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, hne⟩
      rw [hT1, Finset.mem_singleton] at hmem
      exact hr hmem
    have hr₁T : r₁ ∈ T := by rw [hT1]; exact Finset.mem_singleton_self r₁
    have hN_ne : ε r₁ ≠ ∅ := by
      rw [hT] at hr₁T
      exact (Finset.mem_filter.mp hr₁T).2
    have hprod_single : ∏ r ∈ T, orbitSize (ε r) = orbitSize (ε r₁) := by
      rw [hT1]
      simp
    have hN_le : orbitSize (ε r₁) ≤ n := by
      have := hlowT
      rw [hprod_single] at this
      exact le_trans this hdn
    have hN_ge : n ≤ orbitSize (ε r₁) := n_le_orbitSize hn2 (h0 r₁) hN_ne
    have hNeq : orbitSize (ε r₁) = n := le_antisymm hN_le hN_ge
    obtain ⟨j, hSj⟩ := c2slr5_single_of_orbitSize_le hn2 (h0 r₁) hN_ne hN_le
    have hchoose : n.choose j = n := by
      have := hNeq
      rw [hSj, orbitSize_singleton] at this
      exact this
    have hj_nat : (j : ℕ) = 1 ∨ (j : ℕ) + 1 = n := by
      by_contra hnot
      obtain ⟨hj1, hjn⟩ := not_or.mp hnot
      have hj_ne0 : (j : ℕ) ≠ 0 := by
        intro hj0
        have hj_eq : j = (⟨0, by omega⟩ : Fin n) := Fin.ext hj0
        exact h0 r₁ (by rw [hSj, hj_eq]; exact Finset.mem_singleton_self _)
      have hj2 : 2 ≤ (j : ℕ) := by have := j.isLt; omega
      have hjn2 : (j : ℕ) ≤ n - 2 := by have := j.isLt; omega
      have h2le : n.choose 2 ≤ n :=
        (choose_two_le_choose hj2 hjn2).trans (le_of_eq hchoose)
      have hstrict : n + 1 ≤ n.choose 2 := c2slr5_succ_le_choose_two (by omega)
      omega
    have hcardT' : (univ.filter fun r => ε r ≠ ∅).card = 1 := by
      rw [← hT]
      exact hcardT
    have hsf : s = f :=
      c2slr5_s_eq_f_of_unique_active (by omega : 1 ≤ s) ε hmin hper hcardT'
    refine Or.inl ⟨r₁, j, huniq, hSj, hj_nat, hsf, ?_⟩
    rcases hs23 with h | h <;> omega

end CFSG.LocalAnalysis.WeakClosure81
