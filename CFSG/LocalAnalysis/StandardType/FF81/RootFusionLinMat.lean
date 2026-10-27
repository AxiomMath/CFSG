module

public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinCent
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.GroupTheory.Index

public section

namespace CFSG.StandardType.FF81.RootFusionLin

open Matrix

private theorem single_mul_single_left (d : ℕ) (p q x y : Fin d) (c e : ZMod 2) :
    single p q c * single x y e = if q = x then single p y (c * e) else 0 := by
  split_ifs with h
  · rw [h, Matrix.single_mul_single_same c p x y e]
  · exact Matrix.single_mul_single_of_ne c p q x h e

private theorem single_mul_single_right (d : ℕ) (p q x y : Fin d) (c e : ZMod 2) :
    single x y e * single p q c = if y = p then single x q (e * c) else 0 := by
  split_ifs with h
  · rw [h, Matrix.single_mul_single_same e x p q c]
  · exact Matrix.single_mul_single_of_ne e x y p h c

private theorem transvection_mul_single (d : ℕ) (p q a b : Fin d) (c e : ZMod 2) :
    Matrix.transvection p q c * single a b e =
      single a b e + (if q = a then single p b (c * e) else 0) := by
  rw [Matrix.transvection, Matrix.add_mul, Matrix.one_mul, single_mul_single_left d p q a b c e]

private theorem single_mul_transvection (d : ℕ) (p q a b : Fin d) (c e : ZMod 2) :
    single a b e * Matrix.transvection p q c =
      single a b e + (if b = p then single a q (e * c) else 0) := by
  rw [Matrix.transvection, Matrix.mul_add, Matrix.mul_one, single_mul_single_right d p q a b c e]

private theorem mat_add_self (d : ℕ) (X : Matrix (Fin d) (Fin d) (ZMod 2)) : X + X = 0 := by
  ext i j; exact CharTwo.add_self_eq_zero _

private theorem mat_add_cancel_left (d : ℕ) (a b : Matrix (Fin d) (Fin d) (ZMod 2)) :
    a + (a + b) = b := by rw [← add_assoc, mat_add_self, zero_add]

private theorem mat_add_cancel_right (d : ℕ) (a b : Matrix (Fin d) (Fin d) (ZMod 2)) :
    a + b + b = a := by rw [add_assoc, mat_add_self, add_zero]

private theorem mat_neg_eq {d : ℕ} (X : Matrix (Fin d) (Fin d) (ZMod 2)) : -X = X := by
  ext i j; exact CharTwo.neg_eq (X i j)

private def deltaM (d : ℕ) (E : Matrix (Fin d) (Fin d) (ZMod 2))
    (A : Matrix (Fin d) (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2) :=
  (1 + E) * A * (1 + E) + A

private theorem deltaM_deltaM (d : ℕ) (A E F : Matrix (Fin d) (Fin d) (ZMod 2))
    (hEF : E * F = 0) (hFE : F * E = 0) (hEE : E * E = 0) (hFF : F * F = 0) :
    deltaM d E (deltaM d F A) = E * A * F + F * A * E := by
  have hcl := mat_add_cancel_left d
  have hcr := mat_add_cancel_right d
  have hadd := mat_add_self d
  have hEF' : ∀ X : Matrix (Fin d) (Fin d) (ZMod 2), E * (F * X) = 0 :=
    fun X => by rw [← Matrix.mul_assoc, hEF, Matrix.zero_mul]
  have hFE' : ∀ X : Matrix (Fin d) (Fin d) (ZMod 2), F * (E * X) = 0 :=
    fun X => by rw [← Matrix.mul_assoc, hFE, Matrix.zero_mul]
  have hEE' : ∀ X : Matrix (Fin d) (Fin d) (ZMod 2), E * (E * X) = 0 :=
    fun X => by rw [← Matrix.mul_assoc, hEE, Matrix.zero_mul]
  have hFF' : ∀ X : Matrix (Fin d) (Fin d) (ZMod 2), F * (F * X) = 0 :=
    fun X => by rw [← Matrix.mul_assoc, hFF, Matrix.zero_mul]
  unfold deltaM
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
    Matrix.mul_zero, Matrix.zero_mul, hFE, hEF']
  simp only [hadd, hcl, add_zero, add_assoc, add_left_comm, add_comm]

private theorem mem_transvection_conj (d : ℕ) (W : AddSubgroup (Matrix (Fin d) (Fin d) (ZMod 2)))
    (hW : ∀ (P : GL (Fin d) (ZMod 2)), ∀ A ∈ W,
      (P : Matrix (Fin d) (Fin d) (ZMod 2)) * A *
        ((P⁻¹ : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)) ∈ W)
    {i j : Fin d} (hij : i ≠ j) (c : ZMod 2)
    {X : Matrix (Fin d) (Fin d) (ZMod 2)} (hX : X ∈ W) :
    Matrix.transvection i j c * X * Matrix.transvection i j c ∈ W := by
  have hsq : Matrix.transvection i j c * Matrix.transvection i j c = 1 := by
    rw [Matrix.transvection_mul_transvection_same i j hij c c, CharTwo.add_self_eq_zero,
      Matrix.transvection_zero]
  let P : GL (Fin d) (ZMod 2) :=
    ⟨Matrix.transvection i j c, Matrix.transvection i j c, hsq, hsq⟩
  have h := hW P X hX
  simpa [P] using h

private theorem deltaM_mem (d : ℕ) (W : AddSubgroup (Matrix (Fin d) (Fin d) (ZMod 2)))
    (hW : ∀ (P : GL (Fin d) (ZMod 2)), ∀ A ∈ W,
      (P : Matrix (Fin d) (Fin d) (ZMod 2)) * A *
        ((P⁻¹ : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)) ∈ W)
    {i j : Fin d} (hij : i ≠ j) {X : Matrix (Fin d) (Fin d) (ZMod 2)} (hX : X ∈ W) :
    deltaM d (single i j 1) X ∈ W := by
  unfold deltaM
  change Matrix.transvection i j (1 : ZMod 2) * X * Matrix.transvection i j 1 + X ∈ W
  exact W.add_mem (mem_transvection_conj d W hW hij 1 hX) hX

private theorem deltaM_single_row (d : ℕ) (p x y : Fin d) (hpy : p ≠ y) :
    deltaM d (single p x 1) (single x y 1) = single p y 1 := by
  unfold deltaM
  change Matrix.transvection p x (1 : ZMod 2) * single x y 1 * Matrix.transvection p x 1 +
    single x y 1 = single p y 1
  have hconj : Matrix.transvection p x (1 : ZMod 2) * single x y 1 *
      Matrix.transvection p x (1 : ZMod 2) = single x y 1 + single p y 1 := by
    simp only [transvection_mul_single, single_mul_transvection, Matrix.add_mul, mul_one,
      add_zero, if_true, if_neg (Ne.symm hpy)]
  rw [hconj, add_assoc, add_comm (single p y 1) (single x y 1), mat_add_cancel_left]

private theorem deltaM_single_col (d : ℕ) (q x y : Fin d) (hqx : q ≠ x) :
    deltaM d (single y q 1) (single x y 1) = single x q 1 := by
  unfold deltaM
  change Matrix.transvection y q (1 : ZMod 2) * single x y 1 * Matrix.transvection y q 1 +
    single x y 1 = single x q 1
  have hconj : Matrix.transvection y q (1 : ZMod 2) * single x y 1 *
      Matrix.transvection y q (1 : ZMod 2) = single x y 1 + single x q 1 := by
    simp only [transvection_mul_single, single_mul_transvection, mul_one, add_zero, if_true,
      if_neg hqx]
  rw [hconj, add_assoc, add_comm (single x q 1) (single x y 1), mat_add_cancel_left]

private theorem deltaM_single_offdiag (d : ℕ) (i j : Fin d) (_hij : i ≠ j) :
    deltaM d (single j i 1) (single i j 1) =
      single i i 1 + single j j 1 + single j i 1 := by
  unfold deltaM
  change Matrix.transvection j i (1 : ZMod 2) * single i j 1 * Matrix.transvection j i 1 +
    single i j 1 = single i i 1 + single j j 1 + single j i 1
  have hconj : Matrix.transvection j i (1 : ZMod 2) * single i j 1 *
      Matrix.transvection j i (1 : ZMod 2) = single i j 1 + single i i 1 + single j j 1 +
        single j i 1 := by
    simp only [transvection_mul_single, single_mul_transvection, Matrix.add_mul, mul_one,
      if_true]
    abel
  rw [hconj]
  simp only [mat_add_cancel_left, add_assoc, add_left_comm, add_comm]

private theorem transvection_conj_two_units (d : ℕ) (i k p : Fin d) (_hki : k ≠ i)
    (hpi : p ≠ i) (hkp : k ≠ p) (β : ZMod 2) :
    Matrix.transvection k p β * (single i k (1 : ZMod 2) + single i p β) *
        Matrix.transvection k p β = single i k 1 := by
  rw [Matrix.mul_add, Matrix.add_mul,
    transvection_mul_single d k p i k β 1, if_neg hpi, add_zero,
    single_mul_transvection d k p i k β 1, if_pos rfl,
    transvection_mul_single d k p i p β β, if_neg hpi, add_zero,
    single_mul_transvection d k p i p β β, if_neg (Ne.symm hkp)]
  simp only [one_mul, mat_add_cancel_left, add_comm, add_zero]

private theorem single_mul_diagonal (d : ℕ) (i j : Fin d)
    (A : Matrix (Fin d) (Fin d) (ZMod 2)) (hdiag : ∀ a b, a ≠ b → A a b = 0) :
    single i j (1 : ZMod 2) * A = single i j (A j j) := by
  ext a b
  by_cases hai : a = i
  · subst hai
    rw [Matrix.single_mul_apply_same, Matrix.single_apply]
    by_cases hbj : b = j
    · subst hbj; simp
    · simp [Ne.symm hbj, hdiag j b (Ne.symm hbj)]
  · rw [Matrix.single_mul_apply_of_ne (1 : ZMod 2) i j a b hai A, Matrix.single_apply]
    simp [Ne.symm hai]

private theorem diagonal_mul_single (d : ℕ) (i j : Fin d)
    (A : Matrix (Fin d) (Fin d) (ZMod 2)) (hdiag : ∀ a b, a ≠ b → A a b = 0) :
    A * single i j (1 : ZMod 2) = single i j (A i i) := by
  ext a b
  by_cases hbj : b = j
  · subst hbj
    rw [Matrix.mul_single_apply_same, Matrix.single_apply]
    by_cases hai : a = i
    · subst hai; simp
    · simp [Ne.symm hai, hdiag a i hai]
  · rw [Matrix.mul_single_apply_of_ne (1 : ZMod 2) i j a b hbj A, Matrix.single_apply]
    simp [Ne.symm hbj]

private theorem deltaM_single_of_diagonal (d : ℕ) (i j : Fin d) (hij : i ≠ j)
    (A : Matrix (Fin d) (Fin d) (ZMod 2)) (hdiag : ∀ a b, a ≠ b → A a b = 0) :
    deltaM d (single i j 1) A = single i j (A i i + A j j) := by
  have hexp : (1 + single i j (1 : ZMod 2)) * A * (1 + single i j 1) + A =
      single i j 1 * A + A * single i j 1 + single i j 1 * A * single i j 1 := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
    simp only [mat_add_cancel_left, add_assoc, add_left_comm, add_comm]
  have hEAE : single i j (A j j) * single i j (1 : ZMod 2) = 0 :=
    Matrix.single_mul_single_of_ne (A j j) i j i (Ne.symm hij) 1
  unfold deltaM
  rw [hexp, single_mul_diagonal d i j A hdiag, diagonal_mul_single d i j A hdiag, hEAE]
  simp only [add_zero]
  rw [← Matrix.single_add]
  simp only [add_comm]

private theorem zmod_two_eq_zero_or_one (s : ZMod 2) : s = 0 ∨ s = 1 := by
  have hv : s.val = 0 ∨ s.val = 1 := by
    have := ZMod.val_lt s
    omega
  rcases hv with h | h
  · left; rw [← ZMod.natCast_zmod_val s, h]; rfl
  · right; rw [← ZMod.natCast_zmod_val s, h]; rfl

private theorem zmod_two_eq_one_of_ne_zero {c : ZMod 2} (hc : c ≠ 0) : c = 1 := by
  rcases zmod_two_eq_zero_or_one c with h | h
  · exact absurd h hc
  · exact h

private theorem swap_mul_single_unit (d : ℕ) (a b : Fin d) :
    Matrix.swap (ZMod 2) a b * single a b (1 : ZMod 2) = single b b 1 := by
  by_cases hab : a = b
  · subst hab
    rw [Matrix.swap, Equiv.swap_self, Matrix.permMatrix_refl, Matrix.one_mul]
  · ext c e
    by_cases hc : c = a
    · subst hc
      rw [Matrix.swap_mul_apply_left, Matrix.single_apply, Matrix.single_apply]
      simp [hab, Ne.symm hab]
    · by_cases hc' : c = b
      · subst hc'
        rw [Matrix.swap_mul_apply_right, Matrix.single_apply, Matrix.single_apply]
        simp
      · rw [Matrix.swap_mul_of_ne hc hc', Matrix.single_apply, Matrix.single_apply]
        simp [Ne.symm hc, Ne.symm hc']

private theorem single_mul_swap_unit (d : ℕ) (a b : Fin d) :
    single b b (1 : ZMod 2) * Matrix.swap (ZMod 2) a b = single b a 1 := by
  by_cases hab : a = b
  · subst hab
    rw [Matrix.swap, Equiv.swap_self, Matrix.permMatrix_refl, Matrix.mul_one]
  · ext c e
    by_cases he : e = a
    · subst he
      rw [Matrix.mul_swap_apply_left, Matrix.single_apply, Matrix.single_apply]
      simp
    · by_cases he' : e = b
      · subst he'
        rw [Matrix.mul_swap_apply_right, Matrix.single_apply, Matrix.single_apply]
        simp [hab, Ne.symm hab]
      · rw [Matrix.mul_swap_of_ne he he', Matrix.single_apply, Matrix.single_apply]
        simp [Ne.symm he, Ne.symm he']

private theorem swap_conj_single (d : ℕ) (a b : Fin d) :
    Matrix.swap (ZMod 2) a b * single a b (1 : ZMod 2) * Matrix.swap (ZMod 2) a b =
      single b a 1 := by
  rw [swap_mul_single_unit d a b, single_mul_swap_unit d a b]

private theorem mem_single_change_row (d : ℕ) (W : AddSubgroup (Matrix (Fin d) (Fin d) (ZMod 2)))
    (hW : ∀ (P : GL (Fin d) (ZMod 2)), ∀ A ∈ W,
      (P : Matrix (Fin d) (Fin d) (ZMod 2)) * A *
        ((P⁻¹ : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)) ∈ W)
    {x y p : Fin d} (hpx : p ≠ x) (hpy : p ≠ y) (hX : single x y 1 ∈ W) :
    single p y 1 ∈ W := by
  have h := deltaM_mem d W hW hpx hX
  rwa [deltaM_single_row d p x y hpy] at h

private theorem mem_single_change_col (d : ℕ) (W : AddSubgroup (Matrix (Fin d) (Fin d) (ZMod 2)))
    (hW : ∀ (P : GL (Fin d) (ZMod 2)), ∀ A ∈ W,
      (P : Matrix (Fin d) (Fin d) (ZMod 2)) * A *
        ((P⁻¹ : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)) ∈ W)
    {x y q : Fin d} (hqx : q ≠ x) (hqy : q ≠ y) (hX : single x y 1 ∈ W) :
    single x q 1 ∈ W := by
  have h := deltaM_mem d W hW (Ne.symm hqy) hX
  rwa [deltaM_single_col d q x y hqx] at h

theorem trace_eq_zero_mem_of_invariant (d : ℕ) (hd : 3 ≤ d)
    (W : AddSubgroup (Matrix (Fin d) (Fin d) (ZMod 2)))
    (hW : ∀ (P : GL (Fin d) (ZMod 2)), ∀ A ∈ W,
      (P : Matrix (Fin d) (Fin d) (ZMod 2)) * A *
        ((P⁻¹ : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)) ∈ W)
    (A : Matrix (Fin d) (Fin d) (ZMod 2)) (hA : A ∈ W)
    (hnon : ∀ s : ZMod 2, A ≠ s • (1 : Matrix (Fin d) (Fin d) (ZMod 2))) :
    ∀ B : Matrix (Fin d) (Fin d) (ZMod 2), B.trace = 0 → B ∈ W := by
  have hunit : ∃ a b : Fin d, a ≠ b ∧ single a b 1 ∈ W := by
    by_cases hoff : ∃ p q : Fin d, p ≠ q ∧ A p q ≠ 0
    · obtain ⟨p, q, hpq, hpq0⟩ := hoff
      have hk : ∃ k : Fin d, k ≠ p ∧ k ≠ q := by
        have hcard : ({p, q} : Finset (Fin d)).card < (Finset.univ : Finset (Fin d)).card := by
          rw [Finset.card_univ, Fintype.card_fin]
          have h2 : ({p, q} : Finset (Fin d)).card ≤ 2 := by
            rw [Finset.card_insert_of_notMem (by simpa using hpq)]
            simp
          omega
        obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
        exact ⟨k, fun h => hk (by simp [h]), fun h => hk (by simp [h])⟩
      obtain ⟨k, hkp, hkq⟩ := hk
      have hpq1 : A p q = 1 := zmod_two_eq_one_of_ne_zero hpq0
      have hZ : single q k 1 + single q p (A k q) ∈ W := by
        have h1 : deltaM d (single q k 1) A ∈ W := deltaM_mem d W hW (Ne.symm hkq) hA
        have h2 : deltaM d (single q p 1) (deltaM d (single q k 1) A) ∈ W :=
          deltaM_mem d W hW (Ne.symm hpq) h1
        rw [deltaM_deltaM d A (single q p 1) (single q k 1)
          (Matrix.single_mul_single_of_ne (1 : ZMod 2) q p q hpq 1)
          (Matrix.single_mul_single_of_ne (1 : ZMod 2) q k q hkq 1)
          (Matrix.single_mul_single_of_ne (1 : ZMod 2) q p q hpq 1)
          (Matrix.single_mul_single_of_ne (1 : ZMod 2) q k q hkq 1),
          Matrix.single_mul_mul_single, Matrix.single_mul_mul_single] at h2
        simpa [hpq1] using h2
      have hconj : Matrix.transvection k p (A k q) * (single q k 1 + single q p (A k q)) *
          Matrix.transvection k p (A k q) = single q k 1 :=
        transvection_conj_two_units d q k p hkq hpq hkp (A k q)
      have hmem : Matrix.transvection k p (A k q) * (single q k 1 + single q p (A k q)) *
          Matrix.transvection k p (A k q) ∈ W :=
        mem_transvection_conj d W hW hkp (A k q) hZ
      exact ⟨q, k, Ne.symm hkq, by rwa [hconj] at hmem⟩
    · push Not at hoff
      have hdiag : ∀ a b : Fin d, a ≠ b → A a b = 0 := hoff
      let i0 : Fin d := ⟨0, by omega⟩
      have hex : ∃ i j : Fin d, i ≠ j ∧ A i i ≠ A j j := by
        by_contra h
        push Not at h
        refine hnon (A i0 i0) (by
          ext a b
          by_cases hab : a = b
          · subst hab
            rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_apply_eq]
            by_cases hai : a = i0
            · subst hai; rfl
            · exact h a i0 hai
          · rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_apply_ne _ hab]
            exact hdiag a b hab)
      obtain ⟨i, j, hij, hijne⟩ := hex
      have hdelta : deltaM d (single i j 1) A ∈ W := deltaM_mem d W hW hij hA
      have hval : deltaM d (single i j 1) A = single i j (A i i + A j j) :=
        deltaM_single_of_diagonal d i j hij A hdiag
      have hsum : A i i + A j j ≠ 0 := by
        intro h
        apply hijne
        have h' : A i i = -A j j := eq_neg_of_add_eq_zero_left h
        rwa [CharTwo.neg_eq] at h'
      have hone : single i j (A i i + A j j) = single i j (1 : ZMod 2) := by
        rw [zmod_two_eq_one_of_ne_zero hsum]
      exact ⟨i, j, hij, by rwa [hval, hone] at hdelta⟩
  obtain ⟨a, b, hab, hEab⟩ := hunit
  have hEba : single b a 1 ∈ W := by
    have h := hW (GeneralLinearGroup.swap (ZMod 2) a b) (single a b 1) hEab
    have hinv : ((GeneralLinearGroup.swap (ZMod 2) a b : GL (Fin d) (ZMod 2)))⁻¹ =
        GeneralLinearGroup.swap (ZMod 2) a b := Units.ext rfl
    simpa [hinv, swap_conj_single] using h
  have hunits : ∀ i j : Fin d, i ≠ j → single i j 1 ∈ W := by
    intro i j hij
    by_cases hia : i = a
    · rw [hia]
      by_cases hjb : j = b
      · rw [hjb]; exact hEab
      · exact mem_single_change_col d W hW (x := a) (y := b) (q := j)
          (fun h => hij (hia.trans h.symm)) hjb hEab
    · by_cases hib : i = b
      · rw [hib]
        by_cases hja : j = a
        · rw [hja]; exact hEba
        · exact mem_single_change_col d W hW (x := b) (y := a) (q := j)
            (fun h => hij (hib.trans h.symm)) hja hEba
      · by_cases hjb : j = b
        · rw [hjb]
          exact mem_single_change_row d W hW (x := a) (y := b) (p := i) hia hib hEab
        · by_cases hja : j = a
          · rw [hja]
            exact mem_single_change_row d W hW (x := b) (y := a) (p := i) hib hia hEba
          · have hEib : single i b 1 ∈ W :=
              mem_single_change_row d W hW (x := a) (y := b) (p := i) hia hib hEab
            exact mem_single_change_col d W hW (x := i) (y := b) (q := j)
              (Ne.symm hij) hjb hEib
  have hdiagdiff : ∀ i j : Fin d, i ≠ j → single i i 1 + single j j 1 ∈ W := by
    intro i j hij
    have hdelta : deltaM d (single j i 1) (single i j 1) ∈ W :=
      deltaM_mem d W hW (Ne.symm hij) (hunits i j hij)
    have hval : deltaM d (single j i 1) (single i j 1) =
        single i i 1 + single j j 1 + single j i 1 := deltaM_single_offdiag d i j hij
    rw [hval] at hdelta
    have hji : single j i 1 ∈ W := hunits j i (Ne.symm hij)
    have hmem : (single i i 1 + single j j 1 + single j i 1) + single j i 1 ∈ W :=
      W.add_mem hdelta hji
    have heq : (single i i (1 : ZMod 2) + single j j 1 + single j i 1) + single j i 1 =
        single i i (1 : ZMod 2) + single j j 1 := by
      have hC : single j i (1 : ZMod 2) + single j i 1 = 0 := mat_add_self d (single j i 1)
      rw [add_assoc, hC, add_zero]
    rwa [heq] at hmem
  intro B hB
  have hsmul : ∀ (c : ZMod 2) (X : Matrix (Fin d) (Fin d) (ZMod 2)), X ∈ W → c • X ∈ W := by
    intro c X hX
    rcases zmod_two_eq_zero_or_one c with h | h
    · rw [h, zero_smul]; exact W.zero_mem
    · rw [h, one_smul]; exact hX
  have hoff : (∑ i, ∑ j, if i = j then 0 else single i j (B i j)) ∈ W := by
    refine W.sum_mem fun i _ => W.sum_mem fun j _ => ?_
    by_cases hij : i = j
    · rw [if_pos hij]; exact W.zero_mem
    · rw [if_neg hij]
      have : single i j (B i j) = B i j • single i j (1 : ZMod 2) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [this]
      exact hsmul _ _ (hunits i j hij)
  have hdiag : (∑ i, single i i (B i i)) ∈ W := by
    let i0 : Fin d := ⟨0, by omega⟩
    have htrace : (∑ i, B i i) = 0 := by
      simpa [Matrix.trace, Matrix.diag_apply] using hB
    have hzero : (∑ i, B i i • single i0 i0 (1 : ZMod 2)) = 0 := by
      rw [← Finset.sum_smul, htrace, zero_smul]
    have heq : (∑ i, single i i (B i i)) =
        ∑ i, B i i • (single i i 1 + single i0 i0 1) := by
      calc (∑ i, single i i (B i i))
          = ∑ i, B i i • single i i (1 : ZMod 2) := by
            apply Finset.sum_congr rfl; intro i _
            rw [Matrix.smul_single, smul_eq_mul, mul_one]
        _ = (∑ i, B i i • single i i (1 : ZMod 2)) +
              (∑ i, B i i • single i0 i0 (1 : ZMod 2)) := by rw [hzero, add_zero]
        _ = ∑ i, (B i i • single i i (1 : ZMod 2) +
              B i i • single i0 i0 (1 : ZMod 2)) := by rw [Finset.sum_add_distrib]
        _ = ∑ i, B i i • (single i i 1 + single i0 i0 1) := by
            apply Finset.sum_congr rfl; intro i _; rw [smul_add]
    rw [heq]
    refine W.sum_mem fun i _ => ?_
    by_cases hi : i = i0
    · subst hi
      have : single i0 i0 (1 : ZMod 2) + single i0 i0 1 = 0 := mat_add_self d _
      rw [this, smul_zero]; exact W.zero_mem
    · exact hsmul _ _ (hdiagdiff i i0 hi)
  have hsplit : B = (∑ i, ∑ j, if i = j then 0 else single i j (B i j)) +
      ∑ i, single i i (B i i) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single B]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hsingle : single i i (B i i) =
        ∑ j, (if i = j then single i i (B i i) else 0) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hsingle, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [hsplit]
  exact W.add_mem hoff hdiag

theorem card_traceZero (d : ℕ) (hd : 1 ≤ d) :
    Nat.card {B : Matrix (Fin d) (Fin d) (ZMod 2) // B.trace = 0} = 2 ^ (d * d - 1) := by
  have hsurj : Function.Surjective (Matrix.traceAddMonoidHom (Fin d) (ZMod 2)) := by
    intro x
    exact ⟨single ⟨0, by omega⟩ ⟨0, by omega⟩ x, by simp⟩
  have hker : Nat.card (Matrix.traceAddMonoidHom (Fin d) (ZMod 2)).ker * 2 = 2 ^ (d * d) := by
    have h := AddSubgroup.card_ker_mul_card_of_surjective hsurj
    rw [Matrix.card_matrix] at h
    have hcardFin : Nat.card (Fin d) = d := by simp [Nat.card_eq_fintype_card]
    have hcardZ : Nat.card (ZMod 2) = 2 := by simp [Nat.card_eq_fintype_card]
    rw [hcardFin, hcardZ] at h
    exact h
  have hpow : 2 ^ (d * d) = 2 ^ (d * d - 1) * 2 := by
    have hdd : d * d = (d * d - 1) + 1 := by
      have : 1 ≤ d * d := by nlinarith
      omega
    conv_lhs => rw [hdd]
    rw [pow_succ]
  have : Nat.card (Matrix.traceAddMonoidHom (Fin d) (ZMod 2)).ker * 2 =
      2 ^ (d * d - 1) * 2 := by rw [hker, hpow]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) this

theorem card_le_two_of_normal_of_le_zSub (D : Subgroup (GL (BlkIdx 4 0) (ZMod 2)))
    (hDz : D ≤ zSub 4 0) (hDn : ∀ g ∈ Cent 4 0, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hcard : Nat.card D < 2 ^ 15) : Nat.card D ≤ 2 := by
  let W : AddSubgroup (Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
    { carrier := {c | uGL (r := 4) (m := 0) 0 0 c ∈ D}
      zero_mem' := by
        show uGL (r := 4) (m := 0) 0 0 (0 : Matrix (Fin 4) (Fin 4) (ZMod 2)) ∈ D
        simp [uGL_zero]
      add_mem' := by
        intro c c' hc hc'
        show uGL (r := 4) (m := 0) 0 0 (c + c') ∈ D
        have h : uGL (r := 4) (m := 0) 0 0 c * uGL (r := 4) (m := 0) 0 0 c' =
            uGL (r := 4) (m := 0) 0 0 (c + c') := by
          rw [uGL_mul]; simp
        rw [← h]
        exact D.mul_mem hc hc'
      neg_mem' := by
        intro c hc
        show uGL (r := 4) (m := 0) 0 0 (-c) ∈ D
        have h : (uGL (r := 4) (m := 0) 0 0 c)⁻¹ = uGL (r := 4) (m := 0) 0 0 (-c) := by
          rw [uGL_inv]; simp
        rw [← h]
        exact D.inv_mem hc }
  have hcardDW : Nat.card D = Nat.card W := by
    have hf : Function.Bijective
        (fun w : W => (⟨uGL (r := 4) (m := 0) 0 0 w.1, w.2⟩ : D)) := by
      constructor
      · intro x y h
        apply Subtype.ext
        exact (uGL_injective (congrArg Subtype.val h)).2.2
      · rintro ⟨d, hd⟩
        obtain ⟨c, hc⟩ := hDz hd
        refine ⟨⟨c, ?_⟩, Subtype.ext hc.symm⟩
        show uGL (r := 4) (m := 0) 0 0 c ∈ D
        rw [← hc]
        exact hd
    exact (Nat.card_congr (Equiv.ofBijective _ hf)).symm
  have hW : ∀ (P : GL (Fin 4) (ZMod 2)), ∀ A ∈ W,
      (P : Matrix (Fin 4) (Fin 4) (ZMod 2)) * A *
        ((P⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) ∈ W := by
    intro P A hA
    have hlevi : levi P (1 : GL (Fin 0) (ZMod 2)) ∈ Cent 4 0 := levi_mem_cent 4 0 P 1
    have hmem := hDn (levi P 1) hlevi (uGL (r := 4) (m := 0) 0 0 A) hA
    have hconj := levi_conj_uGL 4 0 P (1 : GL (Fin 0) (ZMod 2)) 0 0 A
    rw [hconj] at hmem
    show uGL (r := 4) (m := 0) 0 0 ((P : Matrix (Fin 4) (Fin 4) (ZMod 2)) * A *
      ((P⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) ∈ D
    simpa using hmem
  have hno : ∀ A ∈ W, ∃ s : ZMod 2, A = s • (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
    by_contra h
    push Not at h
    obtain ⟨A, hA, hnon⟩ := h
    have htrace : Nat.card {B : Matrix (Fin 4) (Fin 4) (ZMod 2) // B.trace = 0} ≤ Nat.card W := by
      apply Nat.card_le_card_of_injective (fun B => (⟨B.1,
        trace_eq_zero_mem_of_invariant 4 (by norm_num) W hW A hA hnon B.1 B.2⟩ : W))
      intro B C h
      exact Subtype.ext (congrArg (fun w : W => w.1) h)
    have hcard15 : 2 ^ 15 ≤ Nat.card W := by
      rw [card_traceZero 4 (by norm_num)] at htrace
      norm_num at htrace
      exact htrace
    rw [← hcardDW] at hcard15
    omega
  have hsub : W ≤ AddSubgroup.closure ({1} : Set (Matrix (Fin 4) (Fin 4) (ZMod 2))) := by
    intro A hA
    obtain ⟨s, hs⟩ := hno A hA
    rw [hs]
    rcases zmod_two_eq_zero_or_one s with h | h
    · rw [h, zero_smul]; exact (AddSubgroup.closure _).zero_mem
    · rw [h, one_smul]; exact AddSubgroup.subset_closure (by simp)
  have hclosure :
      Nat.card (AddSubgroup.closure ({1} : Set (Matrix (Fin 4) (Fin 4) (ZMod 2)))) ≤ 2 := by
    have hmem : ∀ A ∈ AddSubgroup.closure ({1} : Set (Matrix (Fin 4) (Fin 4) (ZMod 2))),
        A = 0 ∨ A = 1 := by
      intro A hA
      induction hA using AddSubgroup.closure_induction with
      | mem x hx => rw [Set.mem_singleton_iff] at hx; exact Or.inr hx
      | zero => exact Or.inl rfl
      | add x y hx hy ihx ihy =>
        rcases ihx with rfl | rfl <;> rcases ihy with rfl | rfl <;>
          simp [mat_add_self, zero_add, add_zero]
      | neg x hx ih =>
        rcases ih with rfl | rfl
        · exact Or.inl (mat_neg_eq (0 : Matrix (Fin 4) (Fin 4) (ZMod 2)))
        · exact Or.inr (mat_neg_eq (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    have hfin : Nat.card (AddSubgroup.closure ({1} : Set (Matrix (Fin 4) (Fin 4) (ZMod 2)))) ≤
        Nat.card (Fin 2) := by
      apply Nat.card_le_card_of_injective
        (fun A : AddSubgroup.closure ({1} : Set (Matrix (Fin 4) (Fin 4) (ZMod 2))) =>
          if (A.1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 0 then (0 : Fin 2) else 1)
      intro A B h
      have hA := hmem A.1 A.2
      have hB := hmem B.1 B.2
      rcases hA with hA0 | hA1 <;> rcases hB with hB0 | hB1
      · exact Subtype.ext (hA0.trans hB0.symm)
      · exfalso
        simp [hA0, hB1] at h
      · exfalso
        simp [hA1, hB0] at h
      · exact Subtype.ext (hA1.trans hB1.symm)
    simpa using hfin
  have hcardW : Nat.card W ≤ 2 := by
    have hinj : Function.Injective (fun A : W =>
        (⟨A.1, hsub A.2⟩ : AddSubgroup.closure ({1} : Set (Matrix (Fin 4) (Fin 4) (ZMod 2))))) := by
      intro A B h
      exact Subtype.ext (congrArg
        (fun z : AddSubgroup.closure ({1} : Set (Matrix (Fin 4) (Fin 4) (ZMod 2))) => z.1) h)
    exact le_trans (Nat.card_le_card_of_injective _ hinj) hclosure
  rw [hcardDW]
  exact hcardW

end CFSG.StandardType.FF81.RootFusionLin

end
