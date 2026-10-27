module

public import CFSG.RankThree.PartTwo.Toolkit.Raw

public section

namespace CFSG.RankThree.PartTwo.Toolkit

open Raw

local notation "GL33" => GL (Fin 3) (ZMod 3)

@[expose] def rpowR (x : R9) : ℕ → R9
  | 0 => rone
  | n + 1 => rmul x (rpowR x n)

theorem ofMat_pow (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) (n : ℕ) :
    ofMat (M ^ n) = rpowR (ofMat M) n := by
  induction n with
  | zero => rw [pow_zero, ofMat_one]; rfl
  | succ n ih => rw [pow_succ', ofMat_mul, ih]; rfl

@[expose] def toMat (r : R9) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![r.a, r.b, r.c; r.d, r.e, r.f; r.g, r.h, r.i]

theorem ofMat_toMat (r : R9) : ofMat (toMat r) = r := by
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := r
  rfl

theorem det_toMat (r : R9) : (toMat r).det = rdet r := by
  rw [← rdet_ofMat, ofMat_toMat]

noncomputable def glOf (r : R9) (h : rdet r ≠ 0) : GL33 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (toMat r) (by rwa [det_toMat])

theorem ofMat_glOf (r : R9) (h : rdet r ≠ 0) :
    ofMat ((glOf r h : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = r :=
  ofMat_toMat r

theorem ofMat_glMul (g h : GL33) : ofMat ((g * h : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
    rmul (ofMat g) (ofMat h) := by
  rw [Units.val_mul, ofMat_mul]

theorem ofMat_glPow (g : GL33) (n : ℕ) :
    ofMat ((g ^ n : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = rpowR (ofMat g) n := by
  rw [Units.val_pow_eq_pow_val, ofMat_pow]

theorem ofMat_glOne : ofMat ((1 : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = rone := by
  rw [Units.val_one, ofMat_one]

theorem gl_eq_iff {g h : GL33} : g = h ↔ ofMat (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
    ofMat (h : Matrix (Fin 3) (Fin 3) (ZMod 3)) :=
  ⟨fun e => by rw [e], fun e => Units.ext (ofMat_injective e)⟩

theorem ofMat_inv_of_rmul {g : GL33} {d : R9}
    (h : rmul (ofMat (g : Matrix (Fin 3) (Fin 3) (ZMod 3))) d = rone) :
    ofMat ((g⁻¹ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = d := by
  have h1 : (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) * toMat d = 1 := by
    apply ofMat_injective
    rw [ofMat_mul, ofMat_toMat, h, ofMat_one]
  have h2 : ((g⁻¹ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = toMat d := by
    rw [Matrix.coe_units_inv]
    exact Matrix.inv_eq_right_inv h1
  rw [h2, ofMat_toMat]

theorem exists_gl {r : R9} (h : rdet r ≠ 0) :
    ∃ g : GL33, ofMat (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) = r :=
  ⟨glOf r h, ofMat_glOf r h⟩

end CFSG.RankThree.PartTwo.Toolkit
