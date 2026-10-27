module

public import Mathlib.Tactic.NoncommRing
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Quasithin.H13.L829NK

open Matrix Polynomial

theorem charTwo_prod_identity_of_two {R : Type*} [Ring R] (h2 : (2 : R) = 0) (A B c : R)
    (hc : ∀ x : R, c * x = x * c) (hA : A * A = 0) (hB : B * B = 0)
    (hABA : A * B * A = c * A) (hBAB : B * A * B = c * B) :
    ((1 + A) * (1 + B) + 1) *
      (((1 + A) * (1 + B)) * ((1 + A) * (1 + B)) + c * ((1 + A) * (1 + B)) + 1) = 0 := by
  obtain ⟨N, hN⟩ : ∃ N : R, N = A + B + A * B := ⟨_, rfl⟩
  have hM : (1 + A) * (1 + B) = 1 + N := by rw [hN]; noncomm_ring
  have hAAB : A * (A * B) = 0 := by rw [← mul_assoc, hA, zero_mul]
  have hBAB' : B * (A * B) = c * B := by rw [← mul_assoc]; exact hBAB
  have hABB : A * B * B = 0 := by rw [mul_assoc, hB, mul_zero]
  have hABAB : A * B * (A * B) = c * (A * B) := by
    calc A * B * (A * B) = (A * B * A) * B := by noncomm_ring
      _ = c * (A * B) := by rw [hABA, mul_assoc]
  have hN2 : N * N = A * B + B * A + c * N := by
    calc N * N = A * A + A * B + A * (A * B) + B * A + B * B + B * (A * B) + A * B * A
          + A * B * B + A * B * (A * B) := by rw [hN]; noncomm_ring
      _ = A * B + B * A + c * N := by
        rw [hA, hB, hAAB, hBAB', hABA, hABB, hABAB, hN]
        noncomm_ring
  have hNAB : N * (A * B + B * A) = c * N := by
    calc N * (A * B + B * A) = A * (A * B) + A * B * A + B * (A * B) + B * B * A
          + A * B * (A * B) + A * B * B * A := by rw [hN]; noncomm_ring
      _ = c * N := by
        rw [hAAB, hABA, hBAB', hB, hABAB, hABB, hN]
        noncomm_ring
  have e3 : N * (c * N) = c * (N * N) := by
    calc N * (c * N) = (N * c) * N := by rw [mul_assoc]
      _ = (c * N) * N := by rw [← hc N]
      _ = c * (N * N) := by rw [mul_assoc]
  have hNN : N * (N * N) = c * N + c * (N * N) := by
    calc N * (N * N) = N * (A * B + B * A) + N * (c * N) := by
          rw [hN2]; noncomm_ring
      _ = c * N + c * (N * N) := by rw [hNAB, e3]
  rw [hM]
  have h2' : (1 : R) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
  have e0 : (1 : R) + N + 1 = N := by
    have : (1 : R) + N + 1 = N + (1 + 1) := by abel
    rw [this, h2', add_zero]
  have e1 : (1 + N) * (1 + N) + c * (1 + N) + 1 = N * N + c * N + c := by
    have : (1 + N) * (1 + N) + c * (1 + N) + 1 = N * N + c * N + c + (2 : R) * (1 + N) := by
      noncomm_ring
    rw [this, h2, zero_mul, add_zero]
  rw [e0, e1]
  have e2 : N * (N * N + c * N + c) = N * (N * N) + N * (c * N) + N * c := by noncomm_ring
  have e4 : N * c = c * N := (hc N).symm
  rw [e2, hNN, e3, e4]
  have e5 : c * N + c * (N * N) + c * (N * N) + c * N = (2 : R) * (c * N + c * (N * N)) := by
    noncomm_ring
  rw [e5, h2, zero_mul]

theorem exists_vecMulVec_of_rank_le_one {K : Type*} [Field K] {m n : Type*} [Fintype m]
    [Fintype n] (A : Matrix m n K) (h : A.rank ≤ 1) :
    ∃ (a : m → K) (φ : n → K), A = Matrix.vecMulVec a φ := by
  classical
  have h1 : Module.finrank K (Submodule.span K (Set.range A.row)) ≤ 1 := by
    rw [← Matrix.rank_eq_finrank_span_row]; exact h
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp h1
  have hrow : ∀ i, ∃ c : K, c • (v : n → K) = A.row i := by
    intro i
    obtain ⟨c, hc⟩ := hv ⟨A.row i, Submodule.subset_span ⟨i, rfl⟩⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  choose a ha using hrow
  refine ⟨a, (v : n → K), ?_⟩
  ext i j
  have := congrFun (ha i) j
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.row_apply] at this
  simp [Matrix.vecMulVec_apply, this]

theorem rank_le_one_sandwich {K : Type*} [Field K] {n : ℕ} (A Y : Matrix (Fin n) (Fin n) K)
    (hA : A.rank ≤ 1) : A * Y * A = (A * Y).trace • A := by
  classical
  obtain ⟨a, φ, rfl⟩ := exists_vecMulVec_of_rank_le_one A hA
  ext i l
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.trace, Matrix.diag, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem field_small_cases {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 2 ∨ Nat.card K = 4)
    (x : K) : x = 0 ∨ x = 1 ∨ x ^ 2 + x + 1 = 0 := by
  haveI := Fintype.ofFinite K
  have h := FiniteField.pow_card x
  rw [← Nat.card_eq_fintype_card] at h
  rcases hK with hK | hK
  · rw [hK] at h
    have : x * (x - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (Or.inl (sub_eq_zero.mp h1))
  · rw [hK] at h
    have : x * ((x - 1) * (x ^ 2 + x + 1)) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · rcases mul_eq_zero.mp h1 with h2 | h3
      · exact Or.inr (Or.inl (sub_eq_zero.mp h2))
      · exact Or.inr (Or.inr h3)

theorem pow_eq_one_of_prod_identity {K : Type*} [Field K] [CharP K 2] {R : Type*} [Ring R]
    [Algebra K R] (M : R) (c₀ : K)
    (hid : (M + 1) * (M * M + algebraMap K R c₀ * M + 1) = 0) :
    (c₀ = 0 → M ^ 4 = 1) ∧ (c₀ = 1 → M ^ 3 = 1) ∧ (c₀ ^ 2 + c₀ + 1 = 0 → M ^ 5 = 1) := by
  have h2K : (2 : K) = 0 := by
    have := CharP.cast_eq_zero K 2
    simpa using this
  have h2R : (2 : R) = 0 := by
    have : (2 : R) = algebraMap K R 2 := (map_ofNat (algebraMap K R) 2).symm
    rw [this, h2K, map_zero]
  have h2P : (2 : K[X]) = 0 := by
    have := CharP.cast_eq_zero K[X] 2
    simpa using this
  have h11 : (1 : R) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2R
  have hneg : ∀ y : R, y + 1 = 0 → y = 1 := by
    intro y hy
    calc y = y + 1 + 1 := by rw [add_assoc, h11, add_zero]
      _ = 1 := by rw [hy, zero_add]
  set P : K[X] := (X + 1) * (X ^ 2 + C c₀ * X + 1) with hP
  have hPM : Polynomial.aeval M P = 0 := by
    simp only [hP, map_mul, map_add, map_pow, aeval_X, map_one, aeval_C]
    rw [← hid]
    simp only [pow_two]
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h5 => ?_⟩
  · subst h0
    have e : (X ^ 4 + 1 : K[X]) = (X + 1) * P := by
      rw [hP]
      simp only [map_zero, zero_mul, add_zero]
      linear_combination (-(X ^ 3 + X ^ 2 + X : K[X])) * h2P
    have := congrArg (Polynomial.aeval M) e
    rw [map_mul, hPM, mul_zero] at this
    simp only [map_add, map_pow, aeval_X, map_one] at this
    exact hneg _ this
  · subst h1
    have e : (X ^ 3 + 1 : K[X]) = P := by
      rw [hP]
      simp only [map_one]
      linear_combination (-(X ^ 2 + X : K[X])) * h2P
    have := congrArg (Polynomial.aeval M) e
    rw [hPM] at this
    simp only [map_add, map_pow, aeval_X, map_one] at this
    exact hneg _ this
  · have e : (X ^ 5 + 1 : K[X]) = P * (X ^ 2 + C (c₀ ^ 2) * X + 1) := by
      have hC : (C c₀ ^ 2 + C c₀ + 1 : K[X]) = 0 := by
        have := congrArg (C : K →+* K[X]) h5
        simpa using this
      rw [hP]
      simp only [map_pow]
      linear_combination (-(X ^ 4 + C c₀ * X ^ 3 + C c₀ * X ^ 2 + X : K[X])) * hC
        + (-(X ^ 3 + X ^ 2 : K[X])) * h2P
    have := congrArg (Polynomial.aeval M) e
    rw [map_mul, hPM, zero_mul] at this
    simp only [map_add, map_pow, aeval_X, map_one] at this
    exact hneg _ this

theorem matrix_transvection_prod_pow {K : Type} [Field K] [CharP K 2]
    (hK : ∀ x : K, x = 0 ∨ x = 1 ∨ x ^ 2 + x + 1 = 0) {n : ℕ}
    (T G G' : Matrix (Fin n) (Fin n) K) (hGG' : G * G' = 1) (hG'G : G' * G = 1)
    (hT1 : (T - 1) * (T - 1) = 0) (hT2 : (T - 1).rank ≤ 1) :
    (T * (G' * T * G)) ^ 3 = 1 ∨ (T * (G' * T * G)) ^ 4 = 1 ∨ (T * (G' * T * G)) ^ 5 = 1 := by
  classical
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) K, A = T - 1 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) K, B = G' * T * G - 1 := ⟨_, rfl⟩
  have hTA : T = 1 + A := by rw [hA]; abel
  have hBA : B = G' * A * G := by
    rw [hB, hA]
    calc G' * T * G - 1 = G' * (T - 1) * G + (G' * G - 1) := by noncomm_ring
      _ = G' * (T - 1) * G := by rw [hG'G]; simp
  have hA2 : A * A = 0 := by rw [hA]; exact hT1
  have hB2 : B * B = 0 := by
    rw [hBA]
    calc G' * A * G * (G' * A * G) = G' * A * (G * G') * A * G := by noncomm_ring
      _ = G' * (A * A) * G := by rw [hGG']; noncomm_ring
      _ = 0 := by rw [hA2]; simp
  have hArk : A.rank ≤ 1 := by rw [hA]; exact hT2
  have hBrk : B.rank ≤ 1 := by
    rw [hBA]
    exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans hArk
  have hMdef : T * (G' * T * G) = (1 + A) * (1 + B) := by
    rw [hTA]
    congr 1
    rw [hB, hTA]
    abel
  set c₀ : K := (A * B).trace with hc₀
  have hABA : A * B * A = (c₀ • (1 : Matrix (Fin n) (Fin n) K)) * A := by
    rw [rank_le_one_sandwich A B hArk, smul_mul_assoc, one_mul]
  have hBAB : B * A * B = (c₀ • (1 : Matrix (Fin n) (Fin n) K)) * B := by
    rw [rank_le_one_sandwich B A hBrk, Matrix.trace_mul_comm B A, smul_mul_assoc, one_mul]
  have hcc : ∀ x : Matrix (Fin n) (Fin n) K,
      (c₀ • (1 : Matrix (Fin n) (Fin n) K)) * x = x * (c₀ • (1 : Matrix (Fin n) (Fin n) K)) := by
    intro x
    rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  have h2 : (2 : Matrix (Fin n) (Fin n) K) = 0 := by
    have h2K : (2 : K) = 0 := by
      have := CharP.cast_eq_zero K 2
      simpa using this
    have : (2 : Matrix (Fin n) (Fin n) K) = algebraMap K (Matrix (Fin n) (Fin n) K) 2 :=
      (map_ofNat (algebraMap K (Matrix (Fin n) (Fin n) K)) 2).symm
    rw [this, h2K, map_zero]
  have hid := charTwo_prod_identity_of_two h2 A B (c₀ • (1 : Matrix (Fin n) (Fin n) K)) hcc hA2 hB2
    hABA hBAB
  have hid' : ((1 + A) * (1 + B) + 1) * (((1 + A) * (1 + B)) * ((1 + A) * (1 + B)) +
      algebraMap K (Matrix (Fin n) (Fin n) K) c₀ * ((1 + A) * (1 + B)) + 1) = 0 := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact hid
  rw [hMdef]
  obtain ⟨h4, h3, h5⟩ := pow_eq_one_of_prod_identity ((1 + A) * (1 + B)) c₀ hid'
  rcases hK c₀ with h0 | h1 | h2'
  · exact Or.inr (Or.inl (h4 h0))
  · exact Or.inl (h3 h1)
  · exact Or.inr (Or.inr (h5 h2'))

theorem transvection_mul_conj_pow {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ∨ Nat.card K = 4) {n : ℕ} (t g : GL (Fin n) K)
    (ht1 : ((t : Matrix (Fin n) (Fin n) K) - 1) * ((t : Matrix (Fin n) (Fin n) K) - 1) = 0)
    (ht2 : ((t : Matrix (Fin n) (Fin n) K) - 1).rank ≤ 1) :
    (t * (g⁻¹ * t * g)) ^ 3 = 1 ∨ (t * (g⁻¹ * t * g)) ^ 4 = 1 ∨ (t * (g⁻¹ * t * g)) ^ 5 = 1 := by
  have key := matrix_transvection_prod_pow (field_small_cases hK) (t : Matrix (Fin n) (Fin n) K)
    (g : Matrix (Fin n) (Fin n) K) ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) ht1 ht2
  have e : ∀ k : ℕ, (t * (g⁻¹ * t * g)) ^ k = 1 ↔
      ((t : Matrix (Fin n) (Fin n) K) * (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (t : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K))) ^ k = 1 := by
    intro k
    rw [← Units.val_inj, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_mul, Units.val_mul,
      Units.val_one]
  rw [e 3, e 4, e 5]
  exact key

end CFSG.Quasithin.H13.L829NK
