module

public import Certificates.Data.FF81P51Data
public meta import Certificates.Data.FF81P51Data
public meta import Mathlib.Data.ZMod.Defs
public meta import Mathlib.Data.Matrix.Basic
public meta import Mathlib.Data.Matrix.Mul

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.P51

open Matrix

structure V4 where
  (x0 x1 x2 x3 : ZMod 3)
deriving DecidableEq

structure M16 where
  (a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33 : ZMod 3)
deriving DecidableEq

def V4.toV (x : V4) : V := ![x.x0, x.x1, x.x2, x.x3]

def M16.toM (m : M16) : Mat := !![m.a00, m.a01, m.a02, m.a03; m.a10, m.a11, m.a12, m.a13; m.a20, m.a21, m.a22, m.a23; m.a30, m.a31, m.a32, m.a33]

def V4.zero : V4 := ⟨0, 0, 0, 0⟩

def V4.neg (x : V4) : V4 := ⟨-x.x0, -x.x1, -x.x2, -x.x3⟩

def V4.dot (x y : V4) : ZMod 3 := x.x0 * y.x0 + x.x1 * y.x1 + x.x2 * y.x2 + x.x3 * y.x3

def M16.one : M16 := ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩

def M16.mul (m n : M16) : M16 := ⟨m.a00 * n.a00 + m.a01 * n.a10 + m.a02 * n.a20 + m.a03 * n.a30,
    m.a00 * n.a01 + m.a01 * n.a11 + m.a02 * n.a21 + m.a03 * n.a31,
    m.a00 * n.a02 + m.a01 * n.a12 + m.a02 * n.a22 + m.a03 * n.a32,
    m.a00 * n.a03 + m.a01 * n.a13 + m.a02 * n.a23 + m.a03 * n.a33,
    m.a10 * n.a00 + m.a11 * n.a10 + m.a12 * n.a20 + m.a13 * n.a30,
    m.a10 * n.a01 + m.a11 * n.a11 + m.a12 * n.a21 + m.a13 * n.a31,
    m.a10 * n.a02 + m.a11 * n.a12 + m.a12 * n.a22 + m.a13 * n.a32,
    m.a10 * n.a03 + m.a11 * n.a13 + m.a12 * n.a23 + m.a13 * n.a33,
    m.a20 * n.a00 + m.a21 * n.a10 + m.a22 * n.a20 + m.a23 * n.a30,
    m.a20 * n.a01 + m.a21 * n.a11 + m.a22 * n.a21 + m.a23 * n.a31,
    m.a20 * n.a02 + m.a21 * n.a12 + m.a22 * n.a22 + m.a23 * n.a32,
    m.a20 * n.a03 + m.a21 * n.a13 + m.a22 * n.a23 + m.a23 * n.a33,
    m.a30 * n.a00 + m.a31 * n.a10 + m.a32 * n.a20 + m.a33 * n.a30,
    m.a30 * n.a01 + m.a31 * n.a11 + m.a32 * n.a21 + m.a33 * n.a31,
    m.a30 * n.a02 + m.a31 * n.a12 + m.a32 * n.a22 + m.a33 * n.a32,
    m.a30 * n.a03 + m.a31 * n.a13 + m.a32 * n.a23 + m.a33 * n.a33⟩

def M16.mulV (m : M16) (x : V4) : V4 := ⟨m.a00 * x.x0 + m.a01 * x.x1 + m.a02 * x.x2 + m.a03 * x.x3,
    m.a10 * x.x0 + m.a11 * x.x1 + m.a12 * x.x2 + m.a13 * x.x3,
    m.a20 * x.x0 + m.a21 * x.x1 + m.a22 * x.x2 + m.a23 * x.x3,
    m.a30 * x.x0 + m.a31 * x.x1 + m.a32 * x.x2 + m.a33 * x.x3⟩

def V4.vmul (x : V4) (m : M16) : V4 := ⟨x.x0 * m.a00 + x.x1 * m.a10 + x.x2 * m.a20 + x.x3 * m.a30,
    x.x0 * m.a01 + x.x1 * m.a11 + x.x2 * m.a21 + x.x3 * m.a31,
    x.x0 * m.a02 + x.x1 * m.a12 + x.x2 * m.a22 + x.x3 * m.a32,
    x.x0 * m.a03 + x.x1 * m.a13 + x.x2 * m.a23 + x.x3 * m.a33⟩

def M16.refl (w ψ : V4) : M16 := ⟨1 + w.x0 * ψ.x0,
    w.x0 * ψ.x1,
    w.x0 * ψ.x2,
    w.x0 * ψ.x3,
    w.x1 * ψ.x0,
    1 + w.x1 * ψ.x1,
    w.x1 * ψ.x2,
    w.x1 * ψ.x3,
    w.x2 * ψ.x0,
    w.x2 * ψ.x1,
    1 + w.x2 * ψ.x2,
    w.x2 * ψ.x3,
    w.x3 * ψ.x0,
    w.x3 * ψ.x1,
    w.x3 * ψ.x2,
    1 + w.x3 * ψ.x3⟩

def M16.pow (m : M16) : ℕ → M16
  | 0 => M16.one
  | k + 1 => M16.mul (M16.pow m k) m

def ofColsD (c0 c1 c2 c3 : V4) : M16 := ⟨c0.x0, c1.x0, c2.x0, c3.x0, c0.x1, c1.x1, c2.x1, c3.x1, c0.x2, c1.x2, c2.x2, c3.x2, c0.x3, c1.x3, c2.x3, c3.x3⟩

theorem V4.toV_zero : V4.zero.toV = 0 := by
  ext i; fin_cases i <;> rfl

theorem V4.toV_inj {x y : V4} (h : x.toV = y.toV) : x = y := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  cases x; cases y
  simp_all [V4.toV]

theorem V4.toV_inj_iff {x y : V4} : x.toV = y.toV ↔ x = y := ⟨fun h => V4.toV_inj h, fun h => h ▸ rfl⟩

theorem V4.toV_eq_zero_iff {x : V4} : x.toV = 0 ↔ x = V4.zero := by
  rw [← V4.toV_zero, V4.toV_inj_iff]

theorem M16.toM_inj {m n : M16} (h : m.toM = n.toM) : m = n := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h02 := congrFun (congrFun h 0) 2
  have h03 := congrFun (congrFun h 0) 3
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  have h12 := congrFun (congrFun h 1) 2
  have h13 := congrFun (congrFun h 1) 3
  have h20 := congrFun (congrFun h 2) 0
  have h21 := congrFun (congrFun h 2) 1
  have h22 := congrFun (congrFun h 2) 2
  have h23 := congrFun (congrFun h 2) 3
  have h30 := congrFun (congrFun h 3) 0
  have h31 := congrFun (congrFun h 3) 1
  have h32 := congrFun (congrFun h 3) 2
  have h33 := congrFun (congrFun h 3) 3
  cases m; cases n
  simp_all [M16.toM]

theorem M16.toM_inj_iff {m n : M16} : m.toM = n.toM ↔ m = n := ⟨fun h => M16.toM_inj h, fun h => h ▸ rfl⟩

theorem M16.toM_one : M16.one.toM = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem M16.toM_eq_one_iff {m : M16} : m.toM = 1 ↔ m = M16.one := by
  rw [← M16.toM_one, M16.toM_inj_iff]

theorem M16.toM_mul (m n : M16) : (M16.mul m n).toM = m.toM * n.toM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M16.toM, M16.mul, Matrix.mul_apply, Fin.sum_univ_four]

theorem M16.toM_pow (m : M16) (k : ℕ) : (M16.pow m k).toM = m.toM ^ k := by
  induction k with
  | zero => exact M16.toM_one
  | succ k ih => rw [M16.pow, M16.toM_mul, ih, pow_succ]

theorem M16.toV_mulV (m : M16) (x : V4) : (m.mulV x).toV = m.toM *ᵥ x.toV := by
  ext i
  fin_cases i <;> simp [V4.toV, M16.toM, M16.mulV, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem V4.toV_vmul (x : V4) (m : M16) : (x.vmul m).toV = x.toV ᵥ* m.toM := by
  ext i
  fin_cases i <;> simp [V4.toV, M16.toM, V4.vmul, Matrix.vecMul, dotProduct, Fin.sum_univ_four]

theorem M16.toM_refl (w ψ : V4) : (M16.refl w ψ).toM = 1 + vecMulVec w.toV ψ.toV := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M16.toM, M16.refl, V4.toV, Matrix.one_apply, vecMulVec_apply]

theorem V4.toV_neg (x : V4) : x.neg.toV = -x.toV := by
  ext i; fin_cases i <;> simp [V4.toV, V4.neg]

theorem V4.dot_toV (x y : V4) : x.toV ⬝ᵥ y.toV = V4.dot x y := by
  simp [V4.toV, V4.dot, dotProduct, Fin.sum_univ_four]

def decD (n : ℕ) : V4 := ⟨(n % 3 : ℕ), (n / 3 % 3 : ℕ), (n / 9 % 3 : ℕ), (n / 27 % 3 : ℕ)⟩

def allD : List V4 := (List.range 81).map decD

def nonzeroD : List V4 := (List.range 80).map fun n => decD (n + 1)

def H0D : List M16 :=
  [⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 2, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 1, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 2, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩,
    ⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 2⟩,
    ⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 1⟩,
    ⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2⟩,
    ⟨1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 2, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩,
    ⟨1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 2⟩,
    ⟨1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 1⟩,
    ⟨1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2⟩,
    ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩,
    ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0⟩,
    ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0⟩,
    ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0⟩,
    ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩,
    ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2⟩,
    ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1⟩,
    ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2⟩,
    ⟨1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩,
    ⟨1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0⟩,
    ⟨1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0⟩,
    ⟨1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0⟩,
    ⟨1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩,
    ⟨1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2⟩,
    ⟨1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1⟩,
    ⟨1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2⟩,
    ⟨2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 2, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 1, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 2, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 2, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 1, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩,
    ⟨2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 2⟩,
    ⟨2, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 1⟩,
    ⟨2, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 2⟩,
    ⟨2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 2, 0, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 1, 0, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0⟩,
    ⟨2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩,
    ⟨2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 2⟩,
    ⟨2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 1⟩,
    ⟨2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2⟩,
    ⟨2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩,
    ⟨2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0⟩,
    ⟨2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0⟩,
    ⟨2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0⟩,
    ⟨2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩,
    ⟨2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2⟩,
    ⟨2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1⟩,
    ⟨2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2⟩,
    ⟨2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩,
    ⟨2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0⟩,
    ⟨2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0⟩,
    ⟨2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0⟩,
    ⟨2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩,
    ⟨2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2⟩,
    ⟨2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1⟩,
    ⟨2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2⟩]

def T0D : M16 := ⟨2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩
def S1D : M16 := ⟨1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩
def TauD : M16 := ⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1⟩
def CycD : M16 := ⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0⟩
def Sig01D : M16 := ⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩

def X2D : M16 := M16.mul (M16.mul TauD S1D) TauD

def X3D : M16 := M16.mul (M16.mul CycD X2D) (M16.mul CycD CycD)

def permWD : List M16 :=
  [M16.one, TauD, CycD, M16.mul CycD CycD, M16.mul TauD CycD, M16.mul TauD (M16.mul CycD CycD)]

def H0WD : List M16 :=
  [0, 1].flatMap fun a₀ => [0, 1].flatMap fun a₁ => [0, 1].flatMap fun a₂ =>
    [0, 1].flatMap fun a₃ => permWD.map fun p =>
      M16.mul (M16.mul (M16.mul (M16.mul (M16.pow T0D a₀) (M16.pow S1D a₁)) (M16.pow X2D a₂))
        (M16.pow X3D a₃)) p

def e0D : V4 := ⟨1, 0, 0, 0⟩

def repD : Fin 7 → V4 :=
  ![⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩, ⟨0, 0, 1, 1⟩, ⟨0, 1, 1, 1⟩, ⟨1, 0, 0, 1⟩, ⟨1, 0, 1, 1⟩, ⟨1, 1, 1, 1⟩]

def okLD : Fin 7 → List V4 :=
  ![[⟨1, 0, 0, 0⟩], [⟨0, 0, 0, 1⟩], [⟨0, 0, 2, 2⟩], [], [⟨1, 0, 0, 0⟩, ⟨2, 0, 0, 2⟩],
    [⟨1, 0, 0, 0⟩, ⟨2, 0, 1, 1⟩], [⟨1, 0, 0, 0⟩, ⟨1, 1, 1, 1⟩, ⟨1, 2, 2, 2⟩]]

def V4.get (x : V4) : ℕ → ZMod 3
  | 0 => x.x0
  | 1 => x.x1
  | 2 => x.x2
  | _ => x.x3

def V4.smul (a : ZMod 3) (x : V4) : V4 := ⟨a * x.x0, a * x.x1, a * x.x2, a * x.x3⟩

def eD : ℕ → V4
  | 0 => ⟨1, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0⟩
  | _ => ⟨0, 0, 0, 1⟩

def wtD (x : V4) : ℕ :=
  (if x.x1 ≠ 0 then 1 else 0) + (if x.x2 ≠ 0 then 1 else 0) + (if x.x3 ≠ 0 then 1 else 0)

def orbOfD (x : V4) : Fin 7 :=
  if x.x0 = 0 then (if wtD x = 1 then 1 else if wtD x = 2 then 2 else 3)
  else (if wtD x = 0 then 0 else if wtD x = 1 then 4 else if wtD x = 2 then 5 else 6)

def hOfD (x : V4) : M16 :=
  let k := wtD x
  let idx : List ℕ := [1, 2, 3]
  let pairs := List.zip (idx.take (3 - k) ++ idx.drop (3 - k))
    (idx.filter (fun j => decide (x.get j = 0)) ++ idx.filter (fun j => decide (x.get j ≠ 0)))
  let col : ℕ → V4 := fun i =>
    match pairs.lookup i with
    | some j => V4.smul (if x.get j = 0 then 1 else x.get j) (eD j)
    | none => V4.zero
  ofColsD (V4.smul (if x.x0 = 0 then 1 else x.x0) (eD 0)) (col 1) (col 2) (col 3)

def tabD (x : V4) : Fin 7 × M16 := (orbOfD x, hOfD x)

abbrev CfgD := (Fin 7 → Bool) × (Fin 7 → V4)

def toCfg (c : CfgD) : Cfg := (c.1, fun k => (c.2 k).toV)

def memOmD (c : CfgD) (x : V4) : Bool := decide (x ≠ V4.zero) && c.1 (tabD x).1

def psiCD (c : CfgD) (x : V4) : V4 := (tabD x).2.mulV (c.2 (tabD x).1)

def rCD (c : CfgD) (x : V4) : M16 := M16.refl x (psiCD c x)

def C1D (c : CfgD) : Prop :=
  ∀ w ∈ nonzeroD, memOmD c w = true → ∀ w' ∈ nonzeroD, memOmD c w' = true →
    memOmD c ((rCD c w).mulV w') = true ∧ psiCD c ((rCD c w).mulV w') = (psiCD c w').vmul (rCD c w)

def C3D (c : CfgD) : Prop := ∃ v ∈ nonzeroD, memOmD c v = true ∧ v.x0 = 0

def C4aD (c : CfgD) (k : ℕ) : Prop :=
  ∀ w ∈ nonzeroD, memOmD c w = true → M16.pow (M16.mul T0D (rCD c w)) k = M16.one

def C4bD (c : CfgD) (k : ℕ) : Prop :=
  ∀ w ∈ nonzeroD, memOmD c w = true → ∀ w' ∈ nonzeroD, memOmD c w' = true →
    M16.pow (M16.mul (rCD c w) (rCD c w')) k = M16.one

def C4D (c : CfgD) (k : ℕ) : Prop := C4aD c k → C4bD c k

def WD (c : CfgD) : Prop :=
  ∃ a ∈ nonzeroD, memOmD c a = true ∧ ∃ b ∈ nonzeroD, memOmD c b = true ∧
    M16.mul (M16.mul (rCD c a) (rCD c b)) Sig01D ∈ H0D

def GoodD (c : CfgD) : Prop :=
  c.1 = mA ∨ (c.1 = mB ∧ WD c) ∨ (c.1 = mC ∧ WD c) ∨ c.1 = mD ∨ c.1 = mE

def optLD (k : Fin 7) (m : Bool) : List V4 := if m then okLD k else [V4.zero]

def mkCfgD (m₁ m₂ m₄ m₅ m₆ : Bool) (p₁ p₂ p₄ p₅ p₆ : V4) : CfgD :=
  (![true, m₁, m₂, false, m₄, m₅, m₆], ![⟨1, 0, 0, 0⟩, p₁, p₂, V4.zero, p₄, p₅, p₆])

def OkBD (w ψ : V4) : Prop :=
  (∀ a ∈ H0D, (a.mulV w = w ∨ a.mulV w = w.neg) →
      M16.mul a (M16.refl w ψ) = M16.mul (M16.refl w ψ) a) ∧
    (((M16.refl w ψ).mulV e0D = e0D ∨ (M16.refl w ψ).mulV e0D = e0D.neg) → M16.refl w ψ ∈ H0D)

instance (c : CfgD) : Decidable (C1D c) := by unfold C1D; infer_instance
instance (c : CfgD) : Decidable (C3D c) := by unfold C3D; infer_instance
instance (c : CfgD) (k : ℕ) : Decidable (C4aD c k) := by unfold C4aD; infer_instance
instance (c : CfgD) (k : ℕ) : Decidable (C4bD c k) := by unfold C4bD; infer_instance
instance (c : CfgD) (k : ℕ) : Decidable (C4D c k) := by unfold C4D; infer_instance
instance (c : CfgD) : Decidable (WD c) := by unfold WD; infer_instance
instance (c : CfgD) : Decidable (GoodD c) := by unfold GoodD; infer_instance
instance (w ψ : V4) : Decidable (OkBD w ψ) := by unfold OkBD; infer_instance

end CFSG.RankThree.PartTwo.Sec21.FF81.P51
