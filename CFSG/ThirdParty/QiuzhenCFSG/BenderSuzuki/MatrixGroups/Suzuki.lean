module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Unitary

namespace CFSG
end CFSG
open CFSG

/-!
# Suzuki matrix groups

This file contains the concrete Suzuki matrix generators over
`GF(2^(2m+1))`. Recognition hypotheses are stated directly at their use sites.
-/

namespace CFSG.BenderSuzuki
namespace MatrixGroups

open scoped _root_.MatrixGroups
open PFAppendixIII

universe w

/--
The standard upper-triangular Suzuki root matrix over `GF(2^(2m+1))`.
The Tits power in these coordinates is `x |-> x^(2^(m+1))`.
-/
@[expose] public noncomputable def SuzukiRootMatrix (m : ℕ)
    (a b : BinaryGaloisField (2 * m + 1)) :
    Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1)) :=
  !![1, a, b, a ^ (2 + 2 ^ (m + 1)) + a * b + b ^ (2 ^ (m + 1));
     0, 1, a ^ (2 ^ (m + 1)), a ^ (1 + 2 ^ (m + 1)) + b;
     0, 0, 1, a;
     0, 0, 0, 1]

/--
The standard Suzuki torus matrix over `GF(2^(2m+1))`:
`diag(x^(1+2^m), x^(2^m), x^(-2^m), x^(-1-2^m))`.
Negative powers are written as inverses in the field.
-/
@[expose] public noncomputable def SuzukiTorusMatrix (m : ℕ)
    (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1)) :=
  !![((x : BinaryGaloisField (2 * m + 1)) ^ (1 + 2 ^ m)), 0, 0, 0;
     0, ((x : BinaryGaloisField (2 * m + 1)) ^ (2 ^ m)), 0, 0;
     0, 0, ((x : BinaryGaloisField (2 * m + 1)) ^ (2 ^ m))⁻¹, 0;
     0, 0, 0,
       ((x : BinaryGaloisField (2 * m + 1)) ^ (1 + 2 ^ m))⁻¹]

/-- The standard Suzuki Weyl matrix in `GL(4,GF(2^(2m+1)))` coordinates. -/
@[expose] public noncomputable def SuzukiWeylMatrix (m : ℕ) :
    Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1)) :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, 1, 0, 0;
     1, 0, 0, 0]

/-- The standard Suzuki root element in `GL(4,GF(2^(2m+1)))`. -/
@[expose] public noncomputable def SuzukiRootGL (m : ℕ)
    (a b : BinaryGaloisField (2 * m + 1)) :
    GL (Fin 4) (BinaryGaloisField (2 * m + 1)) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (SuzukiRootMatrix m a b) (by
    classical
    have htri : (SuzukiRootMatrix m a b).BlockTriangular id := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [SuzukiRootMatrix] at hij ⊢
    rw [Matrix.det_of_isUpperTriangular htri]
    simp [SuzukiRootMatrix, Fin.prod_univ_four])

/-- The standard Suzuki torus element in `GL(4,GF(2^(2m+1)))`. -/
@[expose] public noncomputable def SuzukiTorusGL (m : ℕ)
    (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    GL (Fin 4) (BinaryGaloisField (2 * m + 1)) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (SuzukiTorusMatrix m x) (by
    classical
    have htri : (SuzukiTorusMatrix m x).BlockTriangular id := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [SuzukiTorusMatrix] at hij ⊢
    rw [Matrix.det_of_isUpperTriangular htri]
    have hx_sigma :
        (x : BinaryGaloisField (2 * m + 1)) ^ (2 ^ m) ≠ 0 :=
      pow_ne_zero _ x.ne_zero
    have hx_outer :
        (x : BinaryGaloisField (2 * m + 1)) ^ (1 + 2 ^ m) ≠ 0 :=
      pow_ne_zero _ x.ne_zero
    simp [SuzukiTorusMatrix, Fin.prod_univ_four, hx_sigma, hx_outer])

/-- The standard Suzuki Weyl element in `GL(4,GF(2^(2m+1)))`. -/
@[expose] public noncomputable def SuzukiWeylGL (m : ℕ) :
    GL (Fin 4) (BinaryGaloisField (2 * m + 1)) :=
  { val := SuzukiWeylMatrix m
    inv := SuzukiWeylMatrix m
    val_inv := by
      classical
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four]
    inv_val := by
      classical
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four] }

/-- The explicit generator set for `Sz(2^(2m+1))`. -/
@[expose] public def SuzukiMatrixGeneratorSet (m : ℕ) :
    Set (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
  {A | (∃ a b, A = SuzukiRootGL m a b) ∨
    (∃ x, A = SuzukiTorusGL m x) ∨ A = SuzukiWeylGL m}

/-- The concrete Suzuki subgroup generated inside `GL(4,GF(2^(2m+1)))`. -/
@[expose] public noncomputable def SuzukiMatrixSubgroup (m : ℕ) :
    Subgroup (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
  Subgroup.closure (SuzukiMatrixGeneratorSet m)

/-- The finite Suzuki group `Sz(2^(2m+1))` in its concrete matrix model. -/
public noncomputable abbrev SuzukiMatrixGroup (m : ℕ) :=
  SuzukiMatrixSubgroup m

end MatrixGroups
end CFSG.BenderSuzuki
