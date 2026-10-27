module

public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

namespace CFSG.StandardType.ZS

variable {K : Type} [Field K]

@[expose] def pijMat {n : ℕ} (i j : Fin n) (α : K) : Matrix (Fin n) (Fin n) K :=
  fun r c => if r = i ∧ c = j then α else if r = j ∧ c = i then α⁻¹
    else if r = c ∧ r ≠ i ∧ r ≠ j then 1 else 0

@[expose] def diagSignMat {n : ℕ} (i : Fin n) : Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal fun j => if j = i then -1 else 1

@[expose] def halfOnesMat (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  1 - (2 : K)⁻¹ • Matrix.of fun _ _ => 1

@[expose] def weylN4Mats (t : K) : Set (Matrix (Fin 4) (Fin 4) K) :=
  {pijMat 0 1 1, pijMat 1 2 1, pijMat 0 1 t, halfOnesMat 4}

@[expose] def weylEN4Mats (t : K) : Set (Matrix (Fin 4) (Fin 4) K) :=
  insert (diagSignMat 3) (weylN4Mats t)

@[expose] def weylF4Mats : Set (Matrix (Fin 4) (Fin 4) K) :=
  {diagSignMat 0, pijMat 0 1 1, pijMat 1 2 1, halfOnesMat 4}

variable {U : Type} [AddCommGroup U] [Module K U]

@[expose] def basisClosure {n : ℕ} (f : Module.Basis (Fin n) K U)
    (S : Set (Matrix (Fin n) (Fin n) K)) : Subgroup (U ≃ₗ[K] U) :=
  Subgroup.closure {g | LinearMap.toMatrix f f (g : U →ₗ[K] U) ∈ S}

end CFSG.StandardType.ZS
