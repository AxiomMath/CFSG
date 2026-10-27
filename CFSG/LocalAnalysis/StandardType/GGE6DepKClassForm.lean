module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKFormDefs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.StandardType

namespace E6Dep

open Matrix

private theorem evalWord_append {n : ℕ} (g : Fin n → Mat6) (l1 l2 : List (Fin n)) :
    evalWord g (l1 ++ l2) = evalWord g l1 * evalWord g l2 := by
  induction l1 with
  | nil => simp [evalWord]
  | cons i l ih => simp [evalWord, ih, mul_assoc]

private theorem gS_mul_self_all : ∀ i : Fin 5, gS i * gS i = 1 := by decide +kernel

theorem gS_mul_self (i : Fin 5) : gS i * gS i = 1 := gS_mul_self_all i

theorem evalWord_gS_mul_reverse (sw : List (Fin 5)) : evalWord gS sw * evalWord gS sw.reverse = 1 := by
  induction sw with
  | nil => simp [evalWord]
  | cons i l ih =>
    rw [List.reverse_cons, evalWord_append]
    simp only [evalWord, mul_one]
    rw [mul_assoc (gS i), ← mul_assoc (evalWord gS l) (evalWord gS l.reverse) (gS i), ih, one_mul]
    exact gS_mul_self i

private theorem gS_isometry_all : ∀ i : Fin 5, ∀ c : ZMod 3,
    (gS i)ᵀ * gbeta c * gS i = gbeta c := by decide +kernel

private theorem gS_isometry (i : Fin 5) (c : ZMod 3) :
    (gS i)ᵀ * gbeta c * gS i = gbeta c := gS_isometry_all i c

theorem evalWord_gS_isometry (c : ZMod 3) (sw : List (Fin 5)) :
    (evalWord gS sw)ᵀ * gbeta c * evalWord gS sw = gbeta c := by
  induction sw with
  | nil => simp [evalWord]
  | cons i l ih =>
    rw [evalWord, transpose_mul]
    calc
      (evalWord gS l)ᵀ * (gS i)ᵀ * gbeta c * (gS i * evalWord gS l)
          = (evalWord gS l)ᵀ * ((gS i)ᵀ * gbeta c * gS i) * evalWord gS l := by
            simp only [mul_assoc]
      _ = (evalWord gS l)ᵀ * gbeta c * evalWord gS l := by rw [gS_isometry i c]
      _ = gbeta c := ih

private theorem gS_mulVec_xs_all : ∀ i : Fin 5, (gS i).mulVec xs = xs := by decide +kernel

private theorem gS_mulVec_xs (i : Fin 5) : (gS i).mulVec xs = xs := gS_mulVec_xs_all i

private theorem gS_mulVec_xx_all : ∀ i : Fin 5, (gS i).mulVec xx = xx := by decide +kernel

private theorem gS_mulVec_xx (i : Fin 5) : (gS i).mulVec xx = xx := gS_mulVec_xx_all i

theorem evalWord_gS_xs (sw : List (Fin 5)) : (evalWord gS sw).mulVec xs = xs := by
  induction sw with
  | nil => simp [evalWord]
  | cons i l ih =>
    rw [evalWord, ← mulVec_mulVec, ih]
    exact gS_mulVec_xs i

theorem evalWord_gS_xx (sw : List (Fin 5)) : (evalWord gS sw).mulVec xx = xx := by
  induction sw with
  | nil => simp [evalWord]
  | cons i l ih =>
    rw [evalWord, ← mulVec_mulVec, ih]
    exact gS_mulVec_xx i

theorem rK_conj {c : ZMod 3} {s s' : Mat6} (h1 : s * s' = 1) (h2 : sᵀ * gbeta c * s = gbeta c)
    (h : Vec6) : s * rK c h * s' = rK c (s.mulVec h) := by
  have hB : s'ᵀ * gbeta c = gbeta c * s := by
    calc
      s'ᵀ * gbeta c = s'ᵀ * (sᵀ * gbeta c * s) := by rw [h2]
      _ = (s'ᵀ * sᵀ) * gbeta c * s := by simp only [mul_assoc]
      _ = (s * s')ᵀ * gbeta c * s := by rw [← transpose_mul]
      _ = gbeta c * s := by rw [h1, transpose_one, one_mul]
  rw [rK, rK, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hB,
    ← Matrix.mulVec_mulVec, h1]

private theorem rK_std_all : ∀ c t4 t5 : ZMod 3,
    rK c (h0 + t4 • xs + t5 • xx) = gensAll t4 t5 (c * t5 - c * c * t4) (c * t4 - t5) 6 := by
  decide +kernel

theorem rK_std (c t4 t5 : ZMod 3) :
    rK c (h0 + t4 • xs + t5 • xx) = gensAll t4 t5 (c * t5 - c * c * t4) (c * t4 - t5) 6 :=
  rK_std_all c t4 t5

private theorem rK_std_arith_all : ∀ c t4 t5 : ZMod 3, c * t4 - t5 ≠ 0 →
    t4 * (c * t5 - c * c * t4) + t5 * (c * t4 - t5) = 2 ∧
      (c * t5 - c * c * t4) + (c * t4 - t5) * c = 0 := by
  decide +kernel

theorem rK_std_arith (c t4 t5 : ZMod 3) (h : c * t4 - t5 ≠ 0) :
    t4 * (c * t5 - c * c * t4) + t5 * (c * t4 - t5) = 2 ∧
      (c * t5 - c * c * t4) + (c * t4 - t5) * c = 0 :=
  rK_std_arith_all c t4 t5 h

end E6Dep

end CFSG.StandardType

end
