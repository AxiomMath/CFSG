module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrALin
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open Module Matrix

section MatAct

variable {K L : Type*} [Field K] [AddCommGroup L] [Module K L]

theorem matAct_mul (A A' : Matrix (Fin 2) (Fin 2) K) (x : Fin 2 → L) :
    matAct (A * A') x = matAct A (matAct A' x) := by
  funext i
  simp only [matAct_apply, Matrix.mul_apply, Fin.sum_univ_two, add_smul, smul_add, smul_smul]
  abel

theorem matAct_one (x : Fin 2 → L) : matAct (1 : Matrix (Fin 2) (Fin 2) K) x = x := by
  funext i
  fin_cases i <;> simp [matAct_apply]

theorem matAct_add (A A' : Matrix (Fin 2) (Fin 2) K) (x : Fin 2 → L) :
    matAct (A + A') x = matAct A x + matAct A' x := by
  funext i
  simp only [matAct_apply, Matrix.add_apply, add_smul, Pi.add_apply]
  abel

theorem matAct_smul (s : K) (A : Matrix (Fin 2) (Fin 2) K) (x : Fin 2 → L) :
    matAct (s • A) x = s • matAct A x := by
  funext i
  simp only [matAct_apply, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, smul_add, smul_smul]

theorem matAct_pureT (A : Matrix (Fin 2) (Fin 2) K) (f : Fin 2 → K) (y : L) :
    matAct A (pureT f y) = pureT (A *ᵥ f) y := by
  funext i
  simp only [matAct_apply, pureT_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, smul_smul,
    add_smul]

theorem matAct_injective {y : L} (hy : y ≠ 0) {A A' : Matrix (Fin 2) (Fin 2) K}
    (h : ∀ x : Fin 2 → L, matAct A x = matAct A' x) : A = A' := by
  ext i j
  have h1 := congrFun (h (pureT (Pi.single j (1 : K)) y)) i
  rw [matAct_pureT, matAct_pureT, pureT_apply, pureT_apply, Matrix.mulVec_single_one,
    Matrix.mulVec_single_one] at h1
  have h2 : (A i j - A' i j) • y = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr (by simpa [Matrix.col_apply] using h1)
  exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hy)

theorem pureT_left_injective {y : L} (hy : y ≠ 0) {f f' : Fin 2 → K}
    (h : pureT f y = pureT f' y) : f = f' := by
  funext i
  have h1 := congrFun h i
  rw [pureT_apply, pureT_apply, ← sub_eq_zero, ← sub_smul] at h1
  exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hy)

end MatAct

section Root

variable {K : Type*} [Field K]

theorem rootN_mul_self (f : Fin 2 → K) : rootN f * rootN f = 0 := by
  ext i j
  simp only [rootN, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.zero_apply]
  ring

theorem exists_rows_of_mulVec_eq_zero {f : Fin 2 → K} (hf : f ≠ 0)
    {N : Matrix (Fin 2) (Fin 2) K} (hNf : N *ᵥ f = 0) :
    ∃ lam : Fin 2 → K, ∀ i j, N i j = lam i * (![f 1, -f 0] : Fin 2 → K) j := by
  have ha0 : (![f 1, -f 0] : Fin 2 → K) ≠ 0 := by
    intro h
    apply hf
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply,
      neg_eq_zero] at h0 h1
    funext i
    fin_cases i
    · exact h1
    · exact h0
  have hfa : f ⬝ᵥ (![f 1, -f 0] : Fin 2 → K) = 0 := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    ring
  have hrow : ∀ i, ∃ c : K, (fun j => N i j) = c • (![f 1, -f 0] : Fin 2 → K) := by
    intro i
    have hNi : f ⬝ᵥ (fun j => N i j) = 0 := by
      have h := congrFun hNf i
      simp only [Matrix.mulVec, Pi.zero_apply] at h
      rw [dotProduct_comm]
      exact h
    exact exists_eq_smul_of_dotProduct_eq_zero hf ha0 hfa hNi
  choose lam hlam using hrow
  exact ⟨lam, fun i j => by simpa using congrFun (hlam i) j⟩

theorem mul_self_eq_smul_of_rows {N : Matrix (Fin 2) (Fin 2) K} {lam a : Fin 2 → K}
    (hN : ∀ i j, N i j = lam i * a j) : N * N = (lam ⬝ᵥ a) • N := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hN, Matrix.smul_apply, smul_eq_mul, dotProduct]
  ring

theorem exists_eq_smul_rootN {f : Fin 2 → K} (hf : f ≠ 0) {N : Matrix (Fin 2) (Fin 2) K}
    (hNf : N *ᵥ f = 0) (hN2 : N * N = 0) : ∃ s : K, N = s • rootN f := by
  obtain ⟨lam, hNe⟩ := exists_rows_of_mulVec_eq_zero hf hNf
  by_cases hl : lam = 0
  · refine ⟨0, ?_⟩
    ext i j
    rw [hNe, hl, Pi.zero_apply, zero_mul, zero_smul, Matrix.zero_apply]
  have hla : lam ⬝ᵥ (![f 1, -f 0] : Fin 2 → K) = 0 := by
    rw [mul_self_eq_smul_of_rows hNe] at hN2
    rcases smul_eq_zero.mp hN2 with h | h
    · exact h
    · exfalso
      apply hl
      have ha0 : (![f 1, -f 0] : Fin 2 → K) ≠ 0 := by
        intro h'
        apply hf
        have h0 := congrFun h' 0
        have h1 := congrFun h' 1
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply,
          neg_eq_zero] at h0 h1
        funext i
        fin_cases i
        · exact h1
        · exact h0
      obtain ⟨j, hj⟩ : ∃ j, (![f 1, -f 0] : Fin 2 → K) j ≠ 0 := by
        by_contra hh
        push Not at hh
        exact ha0 (funext hh)
      funext i
      have h2 := congrFun (congrFun h i) j
      rw [hNe, Matrix.zero_apply] at h2
      exact (mul_eq_zero.mp h2).resolve_right hj
  have hfa : (![f 1, -f 0] : Fin 2 → K) ⬝ᵥ f = 0 := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    ring
  have ha0 : (![f 1, -f 0] : Fin 2 → K) ≠ 0 := by
    intro h'
    apply hf
    have h0 := congrFun h' 0
    have h1 := congrFun h' 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply,
      neg_eq_zero] at h0 h1
    funext i
    fin_cases i
    · exact h1
    · exact h0
  obtain ⟨s, hs⟩ := exists_eq_smul_of_dotProduct_eq_zero ha0 hf hfa
    (by rw [dotProduct_comm]; exact hla)
  refine ⟨s, ?_⟩
  ext i j
  rw [hNe, hs, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  simp only [rootN, Matrix.of_apply]
  ring

theorem eq_one_add_smul_rootN {f : Fin 2 → K} (hf : f ≠ 0) {A : Matrix (Fin 2) (Fin 2) K}
    {c : K} (hAf : A *ᵥ f = c • f) {m : ℕ} (hm : (A - 1) ^ m = 0) :
    c = 1 ∧ ∃ s : K, A = 1 + s • rootN f := by
  set N := A - 1 with hN
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    have := congrFun (congrFun hm 0) 0
    simp at this
  have hNf : N *ᵥ f = (c - 1) • f := by
    rw [hN, Matrix.sub_mulVec, hAf, Matrix.one_mulVec, sub_smul, one_smul]
  have hNpow : ∀ k : ℕ, (N ^ k) *ᵥ f = (c - 1) ^ k • f := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hNf, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hf (funext hh)
  have hc : c = 1 := by
    have h1 := congrFun (hNpow m) i
    rw [hm, Matrix.zero_mulVec, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at h1
    have h3 := (mul_eq_zero.mp h1.symm).resolve_right hi
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h3)
  have hNf0 : N *ᵥ f = 0 := by rw [hNf, hc, sub_self, zero_smul]
  obtain ⟨lam, hNe⟩ := exists_rows_of_mulVec_eq_zero hf hNf0
  have hpow : ∀ k : ℕ, N ^ (k + 1) = (lam ⬝ᵥ (![f 1, -f 0] : Fin 2 → K)) ^ k • N := by
    intro k
    induction k with
    | zero => rw [zero_add, pow_one, pow_zero, one_smul]
    | succ k ih =>
      rw [pow_succ, ih, smul_mul_assoc, mul_self_eq_smul_of_rows hNe, smul_smul, pow_succ]
  have hN2 : N * N = 0 := by
    rw [mul_self_eq_smul_of_rows hNe]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    rw [hpow k] at hm
    rcases smul_eq_zero.mp hm with h | h
    · rw [eq_zero_of_pow_eq_zero h, zero_smul]
    · rw [h, smul_zero]
  obtain ⟨s, hs⟩ := exists_eq_smul_rootN hf hNf0 hN2
  refine ⟨hc, s, ?_⟩
  rw [← hs, hN, add_sub_cancel]

end Root

end CFSG.RankThree.GF2n.Stroth80.S715L
