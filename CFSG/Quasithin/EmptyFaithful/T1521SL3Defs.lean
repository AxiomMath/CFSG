module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherDescents
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.Positivity.Finset

public noncomputable section

namespace CFSG.Quasithin.L3Aut

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type*} [Field K]

@[expose] def x12 (t : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, t, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def x23 (t : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, 0; 0, 1, t; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def torus (a : Kˣ) : SpecialLinearGroup (Fin 3) K :=
  ⟨!![(a : K), 0, 0; 0, 1, 0; 0, 0, ((a⁻¹ : Kˣ) : K)], by
    simp [Matrix.det_fin_three]⟩

@[simp] theorem coe_x12 (t : K) :
    (x12 t : Matrix (Fin 3) (Fin 3) K) = !![1, t, 0; 0, 1, 0; 0, 0, 1] := rfl

@[simp] theorem coe_x23 (t : K) :
    (x23 t : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 1, t; 0, 0, 1] := rfl

@[simp] theorem coe_torus (a : Kˣ) :
    (torus a : Matrix (Fin 3) (Fin 3) K) =
      !![(a : K), 0, 0; 0, 1, 0; 0, 0, ((a⁻¹ : Kˣ) : K)] := rfl

end CFSG.Quasithin.L3Aut
