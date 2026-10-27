module

import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.H13.S126C

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem one_add_pow_of_cube {N : Matrix ι ι K} (hN : N * N * N = 0) (n : ℕ) :
    (1 + N) ^ n = 1 + (n : K) • N + ((n.choose 2 : ℕ) : K) • (N * N) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, hN, smul_zero, add_zero,
      Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast
    simp only [add_smul, one_smul]
    abel

theorem pow_char_of_cube {p : ℕ} [hp : Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {N : Matrix ι ι K} (hN : N * N * N = 0) : (1 + N) ^ p = 1 := by
  rw [one_add_pow_of_cube hN, CharP.cast_eq_zero, zero_smul, add_zero]
  have hdvd : p ∣ p.choose 2 := Nat.Prime.dvd_choose_self hp.out (by norm_num) (by
    have := hp.out.two_le; omega)
  rw [(CharP.cast_eq_zero_iff K p _).mpr hdvd, zero_smul, add_zero]

variable (bar : K →+* K) (G : Matrix ι ι K)

@[expose] def hrow (x : ι → K) : ι → K := (fun i => bar (x i)) ᵥ* G

variable {bar G}

omit [DecidableEq ι] in
theorem bar_hrow (hbar : ∀ c, bar (bar c) = c) (hG : (G.map bar)ᵀ = G) (x : ι → K) :
    (fun i => bar (hrow bar G x i)) = G *ᵥ x := by
  funext i
  simp only [hrow, vecMul, dotProduct, map_sum, map_mul, hbar, mulVec]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hij : bar (G j i) = G i j := by simpa using congrFun (congrFun hG i) j
  rw [hij, mul_comm]

omit [Fintype ι] [DecidableEq ι] in
theorem map_vecMulVec_bar (a b : ι → K) :
    (vecMulVec a b).map bar = vecMulVec (fun i => bar (a i)) (fun i => bar (b i)) := by
  ext i j
  simp [vecMulVec_apply]

omit [DecidableEq ι] in
theorem adjoint_vecMulVec (hbar : ∀ c, bar (bar c) = c) (hG : (G.map bar)ᵀ = G) (a b : ι → K) :
    ((vecMulVec a (hrow bar G b)).map bar)ᵀ * G = G * vecMulVec b (hrow bar G a) := by
  rw [map_vecMulVec_bar, bar_hrow hbar hG, transpose_vecMulVec, vecMulVec_mul, mul_vecMulVec]
  rfl

omit [DecidableEq ι] in
theorem hrow_neg (x : ι → K) : hrow bar G (-x) = -hrow bar G x := by
  simp only [hrow, Pi.neg_apply, map_neg]
  exact neg_vecMul _ _

omit [DecidableEq ι] in
theorem hrow_smul (c : K) (x : ι → K) : hrow bar G (c • x) = bar c • hrow bar G x := by
  funext j
  simp [hrow, vecMul, dotProduct, Finset.mul_sum, mul_assoc]

theorem hrow_mul_inv {T T' : Matrix ι ι K} (hT : (T.map bar)ᵀ * G * T = G) (hTT : T * T' = 1)
    (x : ι → K) : hrow bar G x ᵥ* T' = hrow bar G (T *ᵥ x) := by
  have h1 : (T.map bar)ᵀ * G = G * T' := by
    calc (T.map bar)ᵀ * G = (T.map bar)ᵀ * G * (T * T') := by rw [hTT, mul_one]
      _ = G * T' := by rw [← mul_assoc, hT]
  simp only [hrow]
  rw [vecMul_vecMul, ← h1, ← vecMul_vecMul]
  congr 1
  funext i
  simp [vecMul, dotProduct, mulVec, map_apply, transpose_apply, mul_comm]

theorem conj_vecMulVec {T T' : Matrix ι ι K} (hT : (T.map bar)ᵀ * G * T = G) (hTT : T * T' = 1)
    (a x : ι → K) :
    T * vecMulVec a (hrow bar G x) * T' = vecMulVec (T *ᵥ a) (hrow bar G (T *ᵥ x)) := by
  rw [mul_vecMulVec, vecMulVec_mul, hrow_mul_inv hT hTT]

variable (bar G) in
@[expose] def eichler (e e₀ : ι → K) (b : K) : Matrix ι ι K :=
  1 + vecMulVec e (hrow bar G e₀) - vecMulVec e₀ (hrow bar G e) + b • vecMulVec e (hrow bar G e)

theorem eichler_mul_eichler_neg {e e₀ : ι → K} {b b' : K} (hee : hrow bar G e ⬝ᵥ e = 0)
    (he₀e : hrow bar G e₀ ⬝ᵥ e = 0) (hee₀ : hrow bar G e ⬝ᵥ e₀ = 0)
    (hb : b + b' + hrow bar G e₀ ⬝ᵥ e₀ = 0) :
    eichler bar G e e₀ b * eichler bar G (-e) e₀ b' = 1 := by
  set E₁ := vecMulVec e (hrow bar G e₀) with hE₁
  set E₂ := vecMulVec e₀ (hrow bar G e) with hE₂
  set E₃ := vecMulVec e (hrow bar G e) with hE₃
  have h11 : E₁ * E₁ = 0 := by rw [vecMulVec_mul_vecMulVec, he₀e, zero_smul, vecMulVec_zero]
  have h12 : E₁ * E₂ = (hrow bar G e₀ ⬝ᵥ e₀) • E₃ := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
  have h13 : E₁ * E₃ = 0 := by rw [vecMulVec_mul_vecMulVec, he₀e, zero_smul, vecMulVec_zero]
  have h21 : E₂ * E₁ = 0 := by rw [vecMulVec_mul_vecMulVec, hee, zero_smul, vecMulVec_zero]
  have h22 : E₂ * E₂ = 0 := by rw [vecMulVec_mul_vecMulVec, hee₀, zero_smul, vecMulVec_zero]
  have h23 : E₂ * E₃ = 0 := by rw [vecMulVec_mul_vecMulVec, hee, zero_smul, vecMulVec_zero]
  have h31 : E₃ * E₁ = 0 := by rw [vecMulVec_mul_vecMulVec, hee, zero_smul, vecMulVec_zero]
  have h32 : E₃ * E₂ = 0 := by rw [vecMulVec_mul_vecMulVec, hee₀, zero_smul, vecMulVec_zero]
  have h33 : E₃ * E₃ = 0 := by rw [vecMulVec_mul_vecMulVec, hee, zero_smul, vecMulVec_zero]
  have hneg : eichler bar G (-e) e₀ b' = 1 - E₁ + E₂ + b' • E₃ := by
    rw [eichler, hrow_neg, neg_vecMulVec, vecMulVec_neg, vecMulVec_neg, neg_vecMulVec, neg_neg]
    abel
  rw [hneg, eichler, ← hE₁, ← hE₂, ← hE₃]
  have hE₃b : (b + b' + hrow bar G e₀ ⬝ᵥ e₀) • E₃ = 0 := by rw [hb, zero_smul]
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    h11, h12, h13, h21, h22, h23, h31, h32, h33, smul_zero, sub_zero, add_zero]
  rw [← sub_eq_zero, ← hE₃b]
  module

omit [Fintype ι] [DecidableEq ι] in
theorem map_smul_bar (c : K) (M : Matrix ι ι K) : (c • M).map bar = bar c • M.map bar := by
  ext i j
  simp

omit [DecidableEq ι] in
theorem adj_add (M N : Matrix ι ι K) :
    ((M + N).map bar)ᵀ * G = (M.map bar)ᵀ * G + (N.map bar)ᵀ * G := by
  rw [Matrix.map_add _ (map_add bar), transpose_add, add_mul]

omit [DecidableEq ι] in
theorem adj_sub (M N : Matrix ι ι K) :
    ((M - N).map bar)ᵀ * G = (M.map bar)ᵀ * G - (N.map bar)ᵀ * G := by
  rw [Matrix.map_sub _ (map_sub bar), transpose_sub, sub_mul]

omit [DecidableEq ι] in
theorem adj_smul (c : K) (M : Matrix ι ι K) :
    ((c • M).map bar)ᵀ * G = bar c • ((M.map bar)ᵀ * G) := by
  rw [map_smul_bar, transpose_smul, smul_mul_assoc]

theorem adj_one : (((1 : Matrix ι ι K)).map bar)ᵀ * G = G := by
  rw [Matrix.map_one _ (map_zero bar) (map_one bar), transpose_one, one_mul]

theorem eichler_neg (e e₀ : ι → K) (b : K) :
    eichler bar G (-e) e₀ b = 1 - vecMulVec e (hrow bar G e₀) + vecMulVec e₀ (hrow bar G e) +
      b • vecMulVec e (hrow bar G e) := by
  rw [eichler, hrow_neg, neg_vecMulVec, vecMulVec_neg, vecMulVec_neg, neg_vecMulVec, neg_neg]
  abel

theorem adjoint_eichler (hbar : ∀ c, bar (bar c) = c) (hG : (G.map bar)ᵀ = G) (e e₀ : ι → K)
    (b : K) : ((eichler bar G e e₀ b).map bar)ᵀ * G = G * eichler bar G (-e) e₀ (bar b) := by
  rw [eichler_neg, eichler, adj_add, adj_sub, adj_add, adj_one, adj_smul,
    adjoint_vecMulVec hbar hG, adjoint_vecMulVec hbar hG, adjoint_vecMulVec hbar hG]
  simp only [mul_add, mul_sub, mul_one, mul_smul_comm]
  abel

theorem eichler_conj {T T' : Matrix ι ι K} (hT : (T.map bar)ᵀ * G * T = G) (hTT : T * T' = 1)
    {e e₀ : ι → K} (he : T *ᵥ e = -e) (he₀ : T *ᵥ e₀ = e₀) (b : K) :
    T * eichler bar G e e₀ b * T' = eichler bar G (-e) e₀ b := by
  rw [eichler, eichler, mul_add, mul_sub, mul_add, mul_one, add_mul, sub_mul, add_mul, hTT,
    mul_smul_comm, smul_mul_assoc, conj_vecMulVec hT hTT, conj_vecMulVec hT hTT,
    conj_vecMulVec hT hTT, he, he₀]

variable (bar G) in
@[expose] def unitTransv (e : ι → K) (t : K) : Matrix ι ι K :=
  1 + t • vecMulVec e (hrow bar G e)

theorem unitTransv_mul_neg {e : ι → K} (hee : hrow bar G e ⬝ᵥ e = 0) (t : K) :
    unitTransv bar G e t * unitTransv bar G e (-t) = 1 := by
  have hN : vecMulVec e (hrow bar G e) * vecMulVec e (hrow bar G e) = 0 := by
    rw [vecMulVec_mul_vecMulVec, hee, zero_smul, vecMulVec_zero]
  simp only [unitTransv, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hN,
    smul_zero, add_zero]
  module

theorem adjoint_unitTransv (hbar : ∀ c, bar (bar c) = c) (hG : (G.map bar)ᵀ = G) (e : ι → K)
    (t : K) : ((unitTransv bar G e t).map bar)ᵀ * G = G * unitTransv bar G e (bar t) := by
  rw [unitTransv, unitTransv, adj_add, adj_one, adj_smul, adjoint_vecMulVec hbar hG, mul_add,
    mul_one, mul_smul_comm]

theorem conj_map_unitTransv (hbar : ∀ c, bar (bar c) = c) (hGb : G.map bar = G) (hGt : Gᵀ = G)
    {A A' : Matrix ι ι K} (hA : (A.map bar)ᵀ * G * A = G) (hAA : A * A' = 1)
    (hAbar : A * A.map bar = 1) {e : ι → K} (he : A *ᵥ (fun i => bar (e i)) = e) (t : K) :
    A * (unitTransv bar G e t).map bar * A' = unitTransv bar G e (bar t) := by
  have hG : (G.map bar)ᵀ = G := by rw [hGb, hGt]
  have hA'A : A' * A = 1 := mul_eq_one_comm.mp hAA
  have hA' : A.map bar = A' := by
    calc A.map bar = A' * A * A.map bar := by rw [hA'A, one_mul]
      _ = A' := by rw [mul_assoc, hAbar, mul_one]
  have hGA : G * A = Aᵀ * G := by
    have h1 : A'ᵀ * G * A = G := by rw [← hA']; exact hA
    calc G * A = (A' * A)ᵀ * G * A := by rw [hA'A, transpose_one, one_mul]
      _ = Aᵀ * (A'ᵀ * G * A) := by rw [transpose_mul]; simp only [mul_assoc]
      _ = Aᵀ * G := by rw [h1]
  have hinj : Function.Injective (fun v : ι → K => fun j => bar (v j)) :=
    fun v w hvw => funext fun j => bar.injective (congrFun hvw j)
  have hbarvec : ∀ (v : ι → K) (M : Matrix ι ι K),
      (fun j => bar ((v ᵥ* M) j)) = (fun i => bar (v i)) ᵥ* M.map bar := fun v M => by
    funext j
    simp [vecMul, dotProduct]
  have hbarmul : ∀ (v : ι → K) (M : Matrix ι ι K),
      (fun j => bar ((M *ᵥ v) j)) = M.map bar *ᵥ (fun i => bar (v i)) := fun v M => by
    funext j
    simp [mulVec, dotProduct]
  have hAbb : A'.map bar = A := by
    rw [← hA']
    ext i j
    simp [hbar]
  have hrowA : (fun i => bar (hrow bar G e i)) ᵥ* A' = hrow bar G e := by
    rw [bar_hrow hbar hG]
    apply hinj
    simp only []
    rw [hbarvec, hbarmul, hGb, hAbb, bar_hrow hbar hG, ← vecMul_transpose G (fun i => bar (e i)),
      hGt, vecMul_vecMul, hGA, ← vecMul_vecMul, vecMul_transpose, he, ← vecMul_transpose, hGt]
  rw [unitTransv, unitTransv, Matrix.map_add _ (map_add bar), map_smul_bar,
    Matrix.map_one _ (map_zero bar) (map_one bar), map_vecMulVec_bar, mul_add, mul_one, add_mul,
    hAA, mul_smul_comm, smul_mul_assoc, mul_vecMulVec, vecMulVec_mul, he, hrowA]

end CFSG.Quasithin.H13.S126C
