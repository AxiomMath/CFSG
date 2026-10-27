module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherDescents
public import CFSG.Quasithin.Vol2.Ch11SecKGBCa
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.C10KG

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

variable {K : Type} [Field K]

@[expose] def dg3 (d : Fin 3 → Kˣ) (hd : d 0 * d 1 * d 2 = 1) : SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal fun i => (d i : K), by
    rw [det_diagonal, Fin.prod_univ_three, ← Units.val_mul, ← Units.val_mul, hd, Units.val_one]⟩

theorem coe_dg3 (d : Fin 3 → Kˣ) (hd : d 0 * d 1 * d 2 = 1) :
    ((dg3 d hd : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal fun i => (d i : K) := rfl

@[expose] def torOne : Kˣ →* SpecialLinearGroup (Fin 3) K where
  toFun a := dg3 ![a, a⁻¹, 1] (by simp)
  map_one' := Subtype.ext (by
    rw [coe_dg3, SpecialLinearGroup.coe_one, ← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp)
  map_mul' a b := Subtype.ext (by
    rw [SpecialLinearGroup.coe_mul, coe_dg3, coe_dg3, coe_dg3, diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [mul_comm])

@[expose] def torTwo : Kˣ →* SpecialLinearGroup (Fin 3) K where
  toFun b := dg3 ![b, b, (b ^ 2)⁻¹] (by simp [pow_two])
  map_one' := Subtype.ext (by
    rw [coe_dg3, SpecialLinearGroup.coe_one, ← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp)
  map_mul' a b := Subtype.ext (by
    rw [SpecialLinearGroup.coe_mul, coe_dg3, coe_dg3, coe_dg3, diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [mul_pow, mul_comm])

theorem coe_torOne (a : Kˣ) : ((torOne a : SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) = diagonal ![(a : K), ((a⁻¹ : Kˣ) : K), 1] := by
  change diagonal _ = _
  congr 1
  ext i
  fin_cases i <;> rfl

theorem coe_torTwo (b : Kˣ) : ((torTwo b : SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) = diagonal ![(b : K), (b : K), (((b ^ 2)⁻¹ : Kˣ) : K)] := by
  change diagonal _ = _
  congr 1
  ext i
  fin_cases i <;> rfl

theorem torOne_mul_torTwo_comm (a b : Kˣ) : torOne a * torTwo b = torTwo b * torOne a :=
  Subtype.ext (by
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_torOne, coe_torTwo,
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    ext i
    exact mul_comm _ _)

variable [CharP K 2]

@[expose] def weylL3 : SpecialLinearGroup (Fin 3) K :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by simp [det_fin_three, CharTwo.neg_eq]⟩

theorem weylL3_mul_self : (weylL3 : SpecialLinearGroup (Fin 3) K) * weylL3 = 1 :=
  Subtype.ext (by
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [weylL3, Matrix.mul_apply, Fin.sum_univ_three])

theorem weylL3_inv : (weylL3 : SpecialLinearGroup (Fin 3) K)⁻¹ = weylL3 :=
  inv_eq_of_mul_eq_one_right weylL3_mul_self

theorem weylL3_conj_diagonal (x y z : K) :
    ((weylL3 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal ![x, y, z] *
      ((weylL3 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal ![y, x, z] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylL3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul_diagonal]

theorem weylL3_conj_torOne (a : Kˣ) :
    weylL3 * torOne a * weylL3⁻¹ = (torOne a : SpecialLinearGroup (Fin 3) K)⁻¹ := by
  rw [weylL3_inv, ← map_inv]
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_torOne, coe_torOne,
    weylL3_conj_diagonal, inv_inv]

theorem weylL3_conj_torTwo (b : Kˣ) :
    weylL3 * torTwo b * weylL3⁻¹ = (torTwo b : SpecialLinearGroup (Fin 3) K) := by
  rw [weylL3_inv]
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_torTwo, weylL3_conj_diagonal]

end CFSG.Quasithin.Vol2.Ch11.SecB.C10KG
