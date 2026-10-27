module

public import CFSG.Monster.B.Fischer.ArrCert
public import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native

@[expose] def f5Mat (a : Array ℕ) : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  Matrix.of fun i j => (a[4 * (i : ℕ) + (j : ℕ)]! : ZMod 5)

@[expose] def f5MulA (a b : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 16) fun k =>
    (a[4 * ((k : ℕ) / 4)]! * b[(k : ℕ) % 4]! + a[4 * ((k : ℕ) / 4) + 1]! * b[4 + (k : ℕ) % 4]! +
      a[4 * ((k : ℕ) / 4) + 2]! * b[8 + (k : ℕ) % 4]! +
      a[4 * ((k : ℕ) / 4) + 3]! * b[12 + (k : ℕ) % 4]!) % 5

theorem f5Mat_mulA (a b : Array ℕ) : f5Mat (f5MulA a b) = f5Mat a * f5Mat b := by
  ext i j
  have hk : 4 * (i : ℕ) + (j : ℕ) < 16 := by omega
  have h1 : (4 * (i : ℕ) + (j : ℕ)) / 4 = i := by omega
  have h2 : (4 * (i : ℕ) + (j : ℕ)) % 4 = j := by omega
  simp only [f5Mat, Matrix.of_apply, f5MulA, Matrix.mul_apply, Fin.sum_univ_four]
  rw [getElem!_pos _ _ (by simpa using hk), Array.getElem_ofFn]
  simp only [h1, h2, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
  have e0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have e1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have e2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [e0, e1, e2, e3, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_one]

@[expose] def f5DetZ (a : Array ℕ) : ℤ :=
  let m := fun (i j : ℕ) => (a[4 * i + j]! : ℤ)
  m 0 0 * (m 1 1 * (m 2 2 * m 3 3 - m 2 3 * m 3 2) - m 1 2 * (m 2 1 * m 3 3 - m 2 3 * m 3 1) +
      m 1 3 * (m 2 1 * m 3 2 - m 2 2 * m 3 1)) -
    m 0 1 * (m 1 0 * (m 2 2 * m 3 3 - m 2 3 * m 3 2) - m 1 2 * (m 2 0 * m 3 3 - m 2 3 * m 3 0) +
      m 1 3 * (m 2 0 * m 3 2 - m 2 2 * m 3 0)) +
    m 0 2 * (m 1 0 * (m 2 1 * m 3 3 - m 2 3 * m 3 1) - m 1 1 * (m 2 0 * m 3 3 - m 2 3 * m 3 0) +
      m 1 3 * (m 2 0 * m 3 1 - m 2 1 * m 3 0)) -
    m 0 3 * (m 1 0 * (m 2 1 * m 3 2 - m 2 2 * m 3 1) - m 1 1 * (m 2 0 * m 3 2 - m 2 2 * m 3 0) +
      m 1 2 * (m 2 0 * m 3 1 - m 2 1 * m 3 0))

theorem f5Mat_det (a : Array ℕ) : (f5Mat a).det = (f5DetZ a : ZMod 5) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.sum_univ_zero, f5Mat, Matrix.of_apply,
    Matrix.submatrix_apply, f5DetZ]
  simp [Fin.succAbove, Fin.succ, Fin.castSucc, Fin.lt_def]
  ring

@[expose] def f5ValidA (a : Array ℕ) : Bool := f5DetZ a % 5 != 0

theorem isUnit_f5Mat {a : Array ℕ} (h : f5ValidA a = true) : IsUnit (f5Mat a) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Matrix.isUnit_iff_isUnit_det, f5Mat_det, isUnit_iff_ne_zero]
  intro h0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  simp only [f5ValidA, bne_iff_ne, ne_eq] at h
  exact h (Int.emod_eq_zero_of_dvd h0)

@[expose] def f5IdA : Array ℕ := #[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]

theorem f5Mat_idA : f5Mat f5IdA = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def f5EqA (a b : Array ℕ) : Bool := (List.range 16).all fun k => a[k]! % 5 == b[k]! % 5

theorem f5Mat_eq_of_eqA {a b : Array ℕ} (h : f5EqA a b = true) : f5Mat a = f5Mat b := by
  ext i j
  simp only [f5EqA, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hk := h (4 * (i : ℕ) + (j : ℕ)) (by omega)
  simp only [f5Mat, Matrix.of_apply]
  rw [← ZMod.natCast_mod, hk, ZMod.natCast_mod]

theorem f5EqA_of_mat_eq {a b : Array ℕ} (h : f5Mat a = f5Mat b) : f5EqA a b = true := by
  simp only [f5EqA, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro k hk
  have := congrFun (congrFun h ⟨k / 4, by omega⟩) ⟨k % 4, by omega⟩
  simp only [f5Mat, Matrix.of_apply, show 4 * (k / 4) + k % 4 = k by omega] at this
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).1 this

end CFSG.RankThree.Native
