module

public import CFSG.Quasithin.Background.FLcR2Mat

public section

namespace CFSG.Quasithin.FLc

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def ix {n : ℕ} (k : ℕ) (h : k < n) : Fin n := ⟨k, h⟩

@[expose] def E01 (n : ℕ) (hn : 3 ≤ n) : SLt n :=
  tv (ix 0 (by omega)) (ix 1 (by omega)) (by simp [ix, Fin.lt_def])

@[expose] def E02 (n : ℕ) (hn : 3 ≤ n) : SLt n :=
  tv (ix 0 (by omega)) (ix 2 (by omega)) (by simp [ix, Fin.lt_def])

@[expose] def E12 (n : ℕ) (hn : 3 ≤ n) : SLt n :=
  tv (ix 1 (by omega)) (ix 2 (by omega)) (by simp [ix, Fin.lt_def])

@[expose] def R1 (n : ℕ) (hn : 3 ≤ n) : SLt n := reflection n (ZMod 2) 1 le_rfl (by omega)

@[expose] def R2 (n : ℕ) (hn : 3 ≤ n) : SLt n := reflection n (ZMod 2) 2 (by norm_num) (by omega)

@[expose] def T1 (n : ℕ) (hn : 3 ≤ n) : SLt n := E01 n hn * R1 n hn

@[expose] def T2 (n : ℕ) (hn : 3 ≤ n) : SLt n := E12 n hn * R2 n hn

theorem node_compute {n : ℕ} (hn : n = 4 ∨ n = 5) (h3 : 3 ≤ n) :
    T1 n h3 * T1 n h3 * T1 n h3 = 1 ∧ T2 n h3 * T2 n h3 * T2 n h3 = 1 ∧
    E02 n h3 * E02 n h3 = 1 ∧
    T2 n h3 * E02 n h3 * (T2 n h3 * T2 n h3) * E02 n h3 = E01 n h3 ∧
    (T2 n h3 * T2 n h3) * E02 n h3 * T2 n h3 * E02 n h3 = E01 n h3 * E02 n h3 ∧
    T1 n h3 * E02 n h3 * (T1 n h3 * T1 n h3) * E02 n h3 = E12 n h3 ∧
    (T1 n h3 * T1 n h3) * E02 n h3 * T1 n h3 * E02 n h3 = E12 n h3 * E02 n h3 := by
  rcases hn with rfl | rfl <;> decide +revert

theorem node_blocks {n : ℕ} (hn : n = 4 ∨ n = 5) (h3 : 3 ≤ n) :
    blk (ix 0 (by omega)) (ix 1 (by omega)) (E02 n h3) = 1 ∧
    blk (ix 1 (by omega)) (ix 2 (by omega)) (E02 n h3) = 1 ∧
    blk (ix 0 (by omega)) (ix 1 (by omega)) (E01 n h3) = tau2 ∧
    blk (ix 1 (by omega)) (ix 2 (by omega)) (E01 n h3) = 1 ∧
    blk (ix 0 (by omega)) (ix 1 (by omega)) (E01 n h3 * E02 n h3) = tau2 ∧
    blk (ix 1 (by omega)) (ix 2 (by omega)) (E01 n h3 * E02 n h3) = 1 ∧
    blk (ix 0 (by omega)) (ix 1 (by omega)) (E12 n h3) = 1 ∧
    blk (ix 1 (by omega)) (ix 2 (by omega)) (E12 n h3) = tau2 ∧
    blk (ix 0 (by omega)) (ix 1 (by omega)) (E12 n h3 * E02 n h3) = 1 ∧
    blk (ix 1 (by omega)) (ix 2 (by omega)) (E12 n h3 * E02 n h3) = tau2 := by
  rcases hn with rfl | rfl <;> decide +revert

theorem node_squares {n : ℕ} (hn : n = 4 ∨ n = 5) (h3 : 3 ≤ n) :
    E01 n h3 * E01 n h3 = 1 ∧ E12 n h3 * E12 n h3 = 1 ∧
    (E01 n h3 * E02 n h3) * (E01 n h3 * E02 n h3) = 1 ∧
    (E12 n h3 * E02 n h3) * (E12 n h3 * E02 n h3) = 1 := by
  rcases hn with rfl | rfl <;> decide +revert

end CFSG.Quasithin.FLc
