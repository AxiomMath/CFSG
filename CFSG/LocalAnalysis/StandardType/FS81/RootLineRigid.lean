module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs
public import CFSG.LocalAnalysis.StandardType.FS81.SpMatAlg
public import CFSG.LocalAnalysis.StandardType.FS81.RootLineRigidAux

public section

namespace CFSG.StandardType.FrameRoute.FS81

open Matrix
open RootLineAux

theorem wt_cases_of_wt_add_sub {n : ℕ} {x y : Coords n} (h1 : wt (x + y) = 2)
    (h2 : wt (x - y) = 2) :
    (wt x = 0 ∧ wt y = 2) ∨ (wt x = 2 ∧ wt y = 0) ∨
      (wt x = 1 ∧ wt y = 1 ∧ ∀ i, x i = 0 ∨ y i = 0) ∨
      (wt x = 2 ∧ wt y = 3) ∨ (wt x = 3 ∧ wt y = 2) ∨
      (wt x = 4 ∧ wt y = 4 ∧ ∀ i, x i = 0 ↔ y i = 0) := by
  have h1' : (sA x y).card + (sB x y).card + (sC x y).card = 2 := by
    rw [← wt_add_eq]
    exact h1
  have h2' : (sA x y).card + (sB x y).card + (sD x y).card = 2 := by
    rw [← wt_sub_eq]
    exact h2
  have hCD : (sD x y).card = (sC x y).card := by omega
  have hwx : wt x = (sA x y).card + (sC x y).card + (sD x y).card := wt_left_eq x y
  have hwy : wt y = (sB x y).card + (sC x y).card + (sD x y).card := wt_right_eq x y
  obtain hC0 | hC1 | hC2 : (sC x y).card = 0 ∨ (sC x y).card = 1 ∨ (sC x y).card = 2 := by
    omega
  · have hD0 : (sD x y).card = 0 := by omega
    have hAB : (sA x y).card + (sB x y).card = 2 := by omega
    obtain hA0 | hA1 | hA2 : (sA x y).card = 0 ∨ (sA x y).card = 1 ∨
        (sA x y).card = 2 := by omega
    · have hB2 : (sB x y).card = 2 := by omega
      left
      exact ⟨by rw [hwx]; omega, by rw [hwy]; omega⟩
    · have hB1 : (sB x y).card = 1 := by omega
      right; right; left
      refine ⟨by rw [hwx]; omega, by rw [hwy]; omega, ?_⟩
      have hC0' : sC x y = ∅ := Finset.card_eq_zero.mp hC0
      have hD0' : sD x y = ∅ := Finset.card_eq_zero.mp hD0
      apply support_disjoint_of_empty_CD
      · intro i
        rw [hC0']
        exact Finset.notMem_empty i
      · intro i
        rw [hD0']
        exact Finset.notMem_empty i
    · have hB0 : (sB x y).card = 0 := by omega
      right; left
      exact ⟨by rw [hwx]; omega, by rw [hwy]; omega⟩
  · have hD1 : (sD x y).card = 1 := by omega
    have hAB : (sA x y).card + (sB x y).card = 1 := by omega
    obtain hA0 | hA1 : (sA x y).card = 0 ∨ (sA x y).card = 1 := by omega
    · have hB1 : (sB x y).card = 1 := by omega
      right; right; right; left
      exact ⟨by rw [hwx]; omega, by rw [hwy]; omega⟩
    · have hB0 : (sB x y).card = 0 := by omega
      right; right; right; right; left
      exact ⟨by rw [hwx]; omega, by rw [hwy]; omega⟩
  · have hD2 : (sD x y).card = 2 := by omega
    have hA0 : (sA x y).card = 0 := by omega
    have hB0 : (sB x y).card = 0 := by omega
    right; right; right; right; right
    refine ⟨by rw [hwx]; omega, by rw [hwy]; omega, ?_⟩
    have hA0' : sA x y = ∅ := Finset.card_eq_zero.mp hA0
    have hB0' : sB x y = ∅ := Finset.card_eq_zero.mp hB0
    apply support_eq_of_empty_AB
    · intro i
      rw [hA0']
      exact Finset.notMem_empty i
    · intro i
      rw [hB0']
      exact Finset.notMem_empty i

private lemma wt_cases_two {n : ℕ} {x y : Coords n} (h1 : wt (x + y) = 2)
    (h2 : wt (x - y) = 2) (hx : wt x = 2) : wt y = 0 ∨ wt y = 3 := by
  rcases wt_cases_of_wt_add_sub h1 h2 with
    ⟨h, _⟩ | ⟨_, hy⟩ | ⟨h, _, _⟩ | ⟨_, hy⟩ | ⟨h, _⟩ | ⟨h, _, _⟩
  · omega
  · exact Or.inl hy
  · omega
  · exact Or.inr hy
  · omega
  · omega

private lemma wt_cases_three {n : ℕ} {x y : Coords n} (h1 : wt (x + y) = 2)
    (h2 : wt (x - y) = 2) (hx : wt x = 3) : wt y = 2 := by
  rcases wt_cases_of_wt_add_sub h1 h2 with
    ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _, _⟩ | ⟨h, _⟩ | ⟨_, hy⟩ | ⟨h, _, _⟩
  all_goals omega

theorem exists_spMat_of_wt_two {n : ℕ} (hn : 5 ≤ n)
    (M : Matrix (Fin n) (Fin n) (ZMod 3))
    (hinv : ∃ N : Matrix (Fin n) (Fin n) (ZMod 3), N * M = 1)
    (h2 : ∀ i j : Fin n, i ≠ j → wt (M *ᵥ (Pi.single i 1 + Pi.single j 1)) = 2 ∧
      wt (M *ᵥ (Pi.single i 1 - Pi.single j 1)) = 2) :
    ∃ σ s, IsSign s ∧ M = spMat σ s := by
  let f : Fin n → Coords n := fun i => M *ᵥ Pi.single i 1
  have hpair : ∀ i j : Fin n, i ≠ j → wt (f i + f j) = 2 ∧ wt (f i - f j) = 2 := by
    intro i j hij
    constructor
    · simpa [f, Matrix.mulVec_add, Matrix.mulVec_single_one] using (h2 i j hij).1
    · simpa [f, Matrix.mulVec_sub, Matrix.mulVec_single_one] using (h2 i j hij).2
  have hf_ne : ∀ i, f i ≠ 0 := by
    intro i hfi
    have hcard : 1 < (Finset.univ.erase i).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨j, k, hjmem, hkmem, hjk⟩ := Finset.one_lt_card_iff.mp hcard
    have hji : j ≠ i := (Finset.mem_erase.mp hjmem).1
    have hki : k ≠ i := (Finset.mem_erase.mp hkmem).1
    have hfj : wt (f j) = 2 := by
      have h := (hpair i j (Ne.symm hji)).1
      rwa [hfi, zero_add] at h
    have hfk : wt (f k) = 2 := by
      have h := (hpair i k (Ne.symm hki)).1
      rwa [hfi, zero_add] at h
    rcases wt_cases_of_wt_add_sub (hpair j k hjk).1 (hpair j k hjk).2 with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _, _⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have hwle : ∀ i, wt (f i) = 1 ∨ wt (f i) = 2 ∨ wt (f i) = 3 ∨ wt (f i) = 4 := by
    intro i
    have hcard : 1 < Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      omega
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hcard i
    rcases wt_cases_of_wt_add_sub (hpair i j (Ne.symm hji)).1
      (hpair i j (Ne.symm hji)).2 with
      ⟨h0, _⟩ | ⟨h2i, _⟩ | ⟨h1i, _, _⟩ | ⟨h2i, _⟩ | ⟨h3i, _⟩ | ⟨h4i, _, _⟩
    · exact absurd (wt_eq_zero_iff.mp h0) (hf_ne i)
    · exact Or.inr (Or.inl h2i)
    · exact Or.inl h1i
    · exact Or.inr (Or.inl h2i)
    · exact Or.inr (Or.inr (Or.inl h3i))
    · exact Or.inr (Or.inr (Or.inr h4i))
  by_cases h1 : ∃ i, wt (f i) = 1
  · obtain ⟨i0, hi0⟩ := h1
    have hw1 : ∀ j, wt (f j) = 1 := by
      intro j
      by_cases hj : j = i0
      · simpa [hj] using hi0
      · have h := hpair i0 j (Ne.symm hj)
        rcases wt_cases_of_wt_add_sub h.1 h.2 with
          ⟨h0, _⟩ | ⟨h2, _⟩ | ⟨hx1, hy, _⟩ | ⟨h2, _⟩ | ⟨h3, _⟩ | ⟨h4, _, _⟩
        · omega
        · omega
        · exact hy
        · omega
        · omega
        · omega
    have hsupp : ∀ j : Fin n, ∃ t : Fin n, f j t ≠ 0 ∧ ∀ u, f j u ≠ 0 → u = t := by
      intro j
      have hcard : (Finset.univ.filter fun r => f j r ≠ 0).card = 1 := by
        simpa [wt] using hw1 j
      obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcard
      refine ⟨t, ?_, ?_⟩
      · have hmem : t ∈ Finset.univ.filter fun r => f j r ≠ 0 := by
          rw [ht]
          exact Finset.mem_singleton_self t
        exact (Finset.mem_filter.mp hmem).2
      · intro u hu
        have hmem : u ∈ Finset.univ.filter fun r => f j r ≠ 0 :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩
        rw [ht] at hmem
        exact Finset.mem_singleton.mp hmem
    choose σ hσ using hsupp
    let s : Fin n → ZMod 3 := fun j => f j (σ j)
    have hσ_inj : Function.Injective σ := by
      intro i j hij
      by_contra hne
      have h := hpair i j hne
      have hwi : wt (f i) = 1 := hw1 i
      have hwj : wt (f j) = 1 := hw1 j
      have hdisj : ∀ t, f i t = 0 ∨ f j t = 0 := by
        rcases wt_cases_of_wt_add_sub h.1 h.2 with
          ⟨h0, _⟩ | ⟨h2, _⟩ | ⟨_, _, hs⟩ | ⟨h2, _⟩ | ⟨h3, _⟩ | ⟨h4, _, _⟩
        · omega
        · omega
        · exact hs
        · omega
        · omega
        · omega
      rcases hdisj (σ i) with h0 | h0
      · exact (hσ i).1 h0
      · rw [hij] at h0
        exact (hσ j).1 h0
    have hσ_bij : Function.Bijective σ := Finite.injective_iff_bijective.mp hσ_inj
    let σe : Equiv.Perm (Fin n) := Equiv.ofBijective σ hσ_bij
    have hsign : IsSign s := fun j => eq_one_or_eq_neg_one_of_ne_zero (s j) (hσ j).1
    have hM : M = spMat σe s := by
      ext i j
      have hcol : f j i = if i = σ j then s j else 0 := by
        by_cases h : i = σ j
        · simp [s, h]
        · have hzero : f j i = 0 := by
            by_contra hne
            exact h ((hσ j).2 i hne)
          simp [h, hzero]
      rw [show M i j = f j i from by simp [f, Matrix.mulVec_single_one], hcol, spMat_apply]
      rfl
    exact ⟨σe, s, hsign, hM⟩
  · push Not at h1
    by_cases h4 : ∃ i, wt (f i) = 4
    · obtain ⟨i0, hi0⟩ := h4
      have hsupp4 : ∀ j, wt (f j) = 4 ∧ ∀ t, f i0 t = 0 ↔ f j t = 0 := by
        intro j
        by_cases hj : j = i0
        · subst hj
          exact ⟨hi0, fun t => Iff.rfl⟩
        · have h := hpair i0 j (Ne.symm hj)
          rcases wt_cases_of_wt_add_sub h.1 h.2 with
            ⟨h0, _⟩ | ⟨h2, _⟩ | ⟨h1, _, _⟩ | ⟨h2, _⟩ | ⟨h3, _⟩ | ⟨_, hy, hs⟩
          · omega
          · omega
          · omega
          · omega
          · omega
          · exact ⟨hy, hs⟩
      have hr : ∃ r : Fin n, f i0 r = 0 := by
        by_contra h
        push Not at h
        have hS : (Finset.univ.filter fun r => f i0 r ≠ 0) = Finset.univ := by
          apply Finset.filter_true_of_mem
          intro r _
          exact h r
        have hcard : (Finset.univ.filter fun r => f i0 r ≠ 0).card = n := by
          rw [hS, Finset.card_univ, Fintype.card_fin]
        have hwt : (Finset.univ.filter fun r => f i0 r ≠ 0).card = 4 := by
          simpa [wt] using hi0
        omega
      obtain ⟨r, hr⟩ := hr
      have hrow : ∀ j, M r j = 0 := by
        intro j
        have hfj : f j r = 0 := ((hsupp4 j).2 r).mp hr
        simpa [f, Matrix.mulVec_single_one] using hfj
      have hdet0 : det M = 0 := Matrix.det_eq_zero_of_row_eq_zero r hrow
      obtain ⟨N, hNM⟩ := hinv
      have hdet1 : det N * det M = 1 := by
        have := congrArg det hNM
        simpa [Matrix.det_mul, Matrix.det_one] using this
      rw [hdet0, mul_zero] at hdet1
      exact False.elim (zero_ne_one hdet1)
    · push Not at h4
      have hw23 : ∀ i, wt (f i) = 2 ∨ wt (f i) = 3 := by
        intro i
        rcases hwle i with h | h | h | h
        · exact absurd h (h1 i)
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h (h4 i)
      let i : Fin n := ⟨0, by omega⟩
      let j : Fin n := ⟨1, by omega⟩
      let k : Fin n := ⟨2, by omega⟩
      have hij : i ≠ j := by
        intro h
        have := congrArg Fin.val h
        simp [i, j] at this
      have hik : i ≠ k := by
        intro h
        have := congrArg Fin.val h
        simp [i, k] at this
      have hjk : j ≠ k := by
        intro h
        have := congrArg Fin.val h
        simp [j, k] at this
      rcases hw23 i with hi | hi
      · have hfj3 : wt (f j) = 3 := by
          rcases wt_cases_two (hpair i j hij).1 (hpair i j hij).2 hi with h0 | h3
          · exact absurd (wt_eq_zero_iff.mp h0) (hf_ne j)
          · exact h3
        have hfk3 : wt (f k) = 3 := by
          rcases wt_cases_two (hpair i k hik).1 (hpair i k hik).2 hi with h0 | h3
          · exact absurd (wt_eq_zero_iff.mp h0) (hf_ne k)
          · exact h3
        have hkj2 := wt_cases_three (hpair j k hjk).1 (hpair j k hjk).2 hfj3
        omega
      · have hfj2 : wt (f j) = 2 :=
          wt_cases_three (hpair i j hij).1 (hpair i j hij).2 hi
        have hfk2 : wt (f k) = 2 :=
          wt_cases_three (hpair i k hik).1 (hpair i k hik).2 hi
        rcases wt_cases_two (hpair j k hjk).1 (hpair j k hjk).2 hfj2 with h0 | h3
        · exact absurd (wt_eq_zero_iff.mp h0) (hf_ne k)
        · omega

theorem exists_spMat_succ_of_wt_two {n : ℕ} (hn : 5 ≤ n)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3))
    (hinv : ∃ N : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3), N * M = 1)
    (h0 : ∀ i, M i 0 = if i = 0 then 1 else 0) (hA : ∀ j : Fin n, M 0 j.succ = 0)
    (h2 : ∀ i j : Fin n, i ≠ j → wt (M *ᵥ (Pi.single i.succ 1 + Pi.single j.succ 1)) = 2 ∧
      wt (M *ᵥ (Pi.single i.succ 1 - Pi.single j.succ 1)) = 2) :
    ∃ σ s, IsSign s ∧ σ 0 = 0 ∧ s 0 = 1 ∧ M = spMat σ s := by
  let M' : Matrix (Fin n) (Fin n) (ZMod 3) := M.submatrix Fin.succ Fin.succ
  have h2' : ∀ i j : Fin n, i ≠ j →
      wt (M' *ᵥ (Pi.single i 1 + Pi.single j 1)) = 2 ∧
      wt (M' *ᵥ (Pi.single i 1 - Pi.single j 1)) = 2 := by
    intro i j hij
    constructor
    · have h := (h2 i j hij).1
      have hsum : (Pi.single i.succ 1 + Pi.single j.succ 1 : Fin (n + 1) → ZMod 3) =
          Fin.cons 0 (Pi.single i 1 + Pi.single j 1) := by
        ext k
        cases k using Fin.cases with
        | zero => simp
        | succ k => simp [single_succ]
      rw [hsum, mulVec_cons_zero M hA, wt_cons_zero] at h
      exact h
    · have h := (h2 i j hij).2
      have hsub : (Pi.single i.succ 1 - Pi.single j.succ 1 : Fin (n + 1) → ZMod 3) =
          Fin.cons 0 (Pi.single i 1 - Pi.single j 1) := by
        ext k
        cases k using Fin.cases with
        | zero => simp
        | succ k => simp [single_succ]
      rw [hsub, mulVec_cons_zero M hA, wt_cons_zero] at h
      exact h
  obtain ⟨N, hNM⟩ := hinv
  let N' : Matrix (Fin n) (Fin n) (ZMod 3) := N.submatrix Fin.succ Fin.succ
  have hN'M' : N' * M' = 1 := by
    ext i j
    have h := congrFun (congrFun hNM i.succ) j.succ
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, hA j, mul_zero, zero_add,
      Matrix.one_apply, Fin.succ_inj] at h ⊢
    exact h
  obtain ⟨σ', s', hsign', hM'eq⟩ := exists_spMat_of_wt_two hn M' ⟨N', hN'M'⟩ h2'
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.Perm.decomposeFin.symm (0, σ')
  let s : Fin (n + 1) → ZMod 3 := Fin.cons 1 s'
  have hσ0 : σ 0 = 0 := by
    simp [σ, Equiv.Perm.decomposeFin_symm_apply_zero]
  have hσsucc : ∀ i : Fin n, σ i.succ = (σ' i).succ := by
    intro i
    simp [σ, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self]
  have hs0 : s 0 = 1 := by
    simp [s]
  have hsign : IsSign s := by
    intro i
    cases i using Fin.cases with
    | zero => left; simp [s]
    | succ j => simpa [s] using hsign' j
  have hM : M = spMat σ s := by
    ext i j
    cases j using Fin.cases with
    | zero =>
      rw [h0 i, spMat_apply, hσ0, hs0]
    | succ j =>
      cases i using Fin.cases with
      | zero =>
        rw [hA j, spMat_apply, hσsucc j]
        have hne : ¬ (0 = (σ' j).succ) := fun hh => Fin.succ_ne_zero (σ' j) hh.symm
        simp [hne]
      | succ i =>
        have h := congrFun (congrFun hM'eq i) j
        rw [show M i.succ j.succ = M' i j from rfl, h, spMat_apply, spMat_apply, hσsucc j]
        by_cases hc : i = σ' j
        · simp [hc, s]
        · have hc' : ¬ (i.succ = (σ' j).succ) := by simpa [Fin.succ_inj] using hc
          simp [hc, hc', s]
  exact ⟨σ, s, hsign, hσ0, hs0, hM⟩

end CFSG.StandardType.FrameRoute.FS81
