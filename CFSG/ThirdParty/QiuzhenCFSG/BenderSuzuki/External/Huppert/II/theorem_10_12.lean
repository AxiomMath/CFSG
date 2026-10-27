module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Unitary
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.RingTheory.RootsOfUnity.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert II.10.12

The statement follows Volume I, physical pages 264-265.  The basis in part (b)
is represented by the displayed standard Gram matrix.  All point sets,
stabilizers, and matrix-coordinate maps are written inline.
-/

namespace CFSG.BenderSuzuki
namespace External

open MatrixGroups
open scoped LinearAlgebra.Projectivization
open scoped Matrix
open scoped commutatorElement

universe u

private theorem hermitian_unitary_preserves_self_pairing
    {K : Type u} [Field K] {n : ℕ} (J : HermitianForm n K)
    (M : J.unitarySubgroup) (v : Fin n → K) :
    let Mmat := ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    dotProduct (fun i => J.conj (Mmat.mulVec v i))
        (J.form.mulVec (Mmat.mulVec v)) =
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) := by
  dsimp only
  letI : Star K := ⟨J.conj⟩
  letI : InvolutiveStar K := ⟨J.conj_involutive⟩
  letI : StarMul K := ⟨fun r s => by
    change J.conj (r * s) = J.conj s * J.conj r
    rw [map_mul, mul_comm]⟩
  letI : StarRing K := ⟨fun r s => by
    change J.conj (r + s) = J.conj r + J.conj s
    rw [map_add]⟩
  let Mmat := ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  change star (Mmat *ᵥ v) ⬝ᵥ J.form *ᵥ (Mmat *ᵥ v) =
    star v ⬝ᵥ J.form *ᵥ v
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul]
  change star v ᵥ*
      (J.conjTranspose Mmat * J.form * Mmat) ⬝ᵥ v = _
  rw [(J.mem_unitarySubgroup_iff (M : GL (Fin n) K)).mp M.property]
  exact (Matrix.dotProduct_mulVec _ _ _).symm


public abbrev hermitianUnipotentCoord
    {K : Type u} [Field K] {n : ℕ} (J : HermitianForm n K) :=
  {z : K × K // z.2 + J.conj z.2 + z.1 * J.conj z.1 = 0}

@[expose] public def hermitianUnipotentMul
    {K : Type u} [Field K] {n : ℕ} (J : HermitianForm n K)
    (z w : hermitianUnipotentCoord J) : hermitianUnipotentCoord J :=
  ⟨(z.1.1 + w.1.1, z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1), by
    dsimp only
    rw [map_sub, map_add, map_add, map_mul, J.conj_involutive]
    linear_combination z.2 + w.2⟩

@[expose] public def hermitianUnipotentOne
    {K : Type u} [Field K] {n : ℕ} (J : HermitianForm n K) :
    hermitianUnipotentCoord J :=
  ⟨(0, 0), by simp⟩

@[expose] public def hermitianUnipotentInv
    {K : Type u} [Field K] {n : ℕ} (J : HermitianForm n K)
    (z : hermitianUnipotentCoord J) : hermitianUnipotentCoord J :=
  ⟨(-z.1.1, J.conj z.1.2), by
    dsimp only
    rw [map_neg, J.conj_involutive]
    linear_combination z.2⟩

public instance hermitianUnipotentCoordMul
    {K : Type u} [Field K] {n : ℕ} (J : HermitianForm n K) :
    Mul (hermitianUnipotentCoord J) :=
  ⟨hermitianUnipotentMul J⟩

public instance hermitianUnipotentCoordOne
    {K : Type u} [Field K] {n : ℕ} (J : HermitianForm n K) :
    One (hermitianUnipotentCoord J) :=
  ⟨hermitianUnipotentOne J⟩

public instance hermitianUnipotentCoordInv
    {K : Type u} [Field K] {n : ℕ} (J : HermitianForm n K) :
    Inv (hermitianUnipotentCoord J) :=
  ⟨hermitianUnipotentInv J⟩

public instance hermitianUnipotentCoordGroup
    {K : Type u} [Field K] {n : ℕ} (J : HermitianForm n K) :
    Group (hermitianUnipotentCoord J) := by
  apply Group.ofLeftAxioms
  · intro x y z
    change hermitianUnipotentMul J (hermitianUnipotentMul J x y) z =
      hermitianUnipotentMul J x (hermitianUnipotentMul J y z)
    apply Subtype.ext
    apply Prod.ext <;> simp only [hermitianUnipotentMul]
    · ring
    · rw [map_add]
      ring
  · intro x
    change hermitianUnipotentMul J (hermitianUnipotentOne J) x = x
    apply Subtype.ext
    apply Prod.ext <;> simp [hermitianUnipotentMul, hermitianUnipotentOne]
  · intro x
    change hermitianUnipotentMul J (hermitianUnipotentInv J x) x =
      hermitianUnipotentOne J
    apply Subtype.ext
    apply Prod.ext <;> simp only [hermitianUnipotentInv,
      hermitianUnipotentMul, hermitianUnipotentOne]
    · ring
    · linear_combination x.2


public theorem hermitianUnipotent_commutator
    {K : Type u} [Field K] {n : ℕ} (J : HermitianForm n K)
    (z w : hermitianUnipotentCoord J) :
    ⁅z, w⁆ =
      ⟨(0, w.1.1 * J.conj z.1.1 - z.1.1 * J.conj w.1.1), by
        dsimp only
        rw [map_sub, map_mul, map_mul, J.conj_involutive,
          J.conj_involutive]
        ring⟩ := by
  change hermitianUnipotentMul J
      (hermitianUnipotentMul J
        (hermitianUnipotentMul J z w) (hermitianUnipotentInv J z))
      (hermitianUnipotentInv J w) = _
  apply Subtype.ext
  apply Prod.ext
  · simp only [hermitianUnipotentMul, hermitianUnipotentInv]
    ring
  · simp only [hermitianUnipotentMul, hermitianUnipotentInv]
    rw [map_neg, map_neg]
    linear_combination z.2 + w.2

@[expose] public def hermitianUnipotentMatrix
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (z : hermitianUnipotentCoord J) : Matrix (Fin 3) (Fin 3) K :=
  !![1, z.1.1, z.1.2; 0, 1, -J.conj z.1.1; 0, 0, 1]

@[simp] public theorem hermitianUnipotentMatrix_eq
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (z : hermitianUnipotentCoord J) :
    hermitianUnipotentMatrix J z =
      !![1, z.1.1, z.1.2; 0, 1, -J.conj z.1.1; 0, 0, 1] :=
  rfl

@[expose] public def hermitianUnipotentGL
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (z : hermitianUnipotentCoord J) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (hermitianUnipotentMatrix J z) (by
    simp [hermitianUnipotentMatrix, Matrix.det_fin_three])

@[simp] public theorem hermitianUnipotentGL_val
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (z : hermitianUnipotentCoord J) :
    (hermitianUnipotentGL J z : Matrix (Fin 3) (Fin 3) K) =
      hermitianUnipotentMatrix J z :=
  rfl

@[expose] public def hermitianUnipotentSU
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    hermitianUnipotentCoord J →* J.specialSubgroup :=
  { toFun := fun z => ⟨hermitianUnipotentGL J z, by
      apply (J.mem_specialSubgroup_iff (hermitianUnipotentGL J z)).mpr
      constructor
      · rw [hJstandard]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [hermitianUnipotentGL, hermitianUnipotentMatrix,
            HermitianForm.conjTranspose, Matrix.mul_apply,
            Fin.sum_univ_three]
        all_goals try rw [J.conj_involutive z.1.1]
        all_goals try linear_combination z.2
        all_goals ring
      · ext
        change (hermitianUnipotentMatrix J z).det = 1
        simp [hermitianUnipotentMatrix, Matrix.det_fin_three]⟩
    map_one' := by
      apply Subtype.ext
      change hermitianUnipotentGL J (hermitianUnipotentOne J) = 1
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change hermitianUnipotentMatrix J (hermitianUnipotentOne J) i j =
        (1 : Matrix (Fin 3) (Fin 3) K) i j
      fin_cases i <;> fin_cases j <;>
        simp [hermitianUnipotentMatrix, hermitianUnipotentOne]
    map_mul' := by
      intro z w
      apply Subtype.ext
      change hermitianUnipotentGL J (hermitianUnipotentMul J z w) =
        hermitianUnipotentGL J z * hermitianUnipotentGL J w
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change hermitianUnipotentMatrix J (hermitianUnipotentMul J z w) i j =
        (hermitianUnipotentMatrix J z * hermitianUnipotentMatrix J w) i j
      fin_cases i <;> fin_cases j <;>
        simp [hermitianUnipotentMatrix, hermitianUnipotentMul,
          Matrix.mul_apply, Fin.sum_univ_three] <;>
        ring }

/-- The Heisenberg root homomorphism in the projective special unitary group. -/
@[expose] public def hermitianUnipotentPSU
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    hermitianUnipotentCoord J →* ProjectiveSpecialUnitaryMatrixGroup J :=
  let f : hermitianUnipotentCoord J →*
      Matrix.ProjGenLinGroup (Fin 3) K :=
    Matrix.ProjGenLinGroup.mk.comp
      (J.specialSubgroup.subtype.comp (hermitianUnipotentSU J hJstandard))
  f.codRestrict (ProjectiveSpecialUnitaryMatrixGroup J) (fun z =>
    Subgroup.mem_map_of_mem Matrix.ProjGenLinGroup.mk
      (hermitianUnipotentSU J hJstandard z).property)

@[simp] public theorem hermitianUnipotentPSU_val
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (z : hermitianUnipotentCoord J) :
    ((hermitianUnipotentPSU J hJstandard z :
        ProjectiveSpecialUnitaryMatrixGroup J) :
      Matrix.ProjGenLinGroup (Fin 3) K) =
        Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J z) :=
  rfl

@[expose] public def hermitianTorusMatrix
    {K : Type u} [Field K] (J : HermitianForm 3 K) (k : Kˣ) :
    Matrix (Fin 3) (Fin 3) K :=
  !![(J.conj (k : K))⁻¹, 0, 0;
     0, J.conj (k : K) * (k : K)⁻¹, 0;
     0, 0, (k : K)]

@[simp] public theorem hermitianTorusMatrix_eq
    {K : Type u} [Field K] (J : HermitianForm 3 K) (k : Kˣ) :
    hermitianTorusMatrix J k =
      !![(J.conj (k : K))⁻¹, 0, 0;
         0, J.conj (k : K) * (k : K)⁻¹, 0;
         0, 0, (k : K)] :=
  rfl

@[expose] public def hermitianTorusGL
    {K : Type u} [Field K] (J : HermitianForm 3 K) (k : Kˣ) :
    GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (hermitianTorusMatrix J k) (by
    have hk : (k : K) ≠ 0 := Units.ne_zero k
    have hconjk : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk
    simp [hermitianTorusMatrix, Matrix.det_fin_three, hk, hconjk])

@[simp] public theorem hermitianTorusGL_val
    {K : Type u} [Field K] (J : HermitianForm 3 K) (k : Kˣ) :
    (hermitianTorusGL J k : Matrix (Fin 3) (Fin 3) K) =
      hermitianTorusMatrix J k :=
  rfl

@[expose] public def hermitianTorusAction
    {K : Type u} [Field K] (J : HermitianForm 3 K) (k : Kˣ)
    (z : hermitianUnipotentCoord J) : hermitianUnipotentCoord J := by
  have hk : (k : K) ≠ 0 := Units.ne_zero k
  have hconjk : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk
  let a' := z.1.1 * (k : K) * (J.conj (k : K))⁻¹ ^ 2
  let b' := z.1.2 * (J.conj (k : K))⁻¹ * (k : K)⁻¹
  have hparam : b' + J.conj b' + a' * J.conj a' = 0 := by
    have hscale :
        z.1.2 * (J.conj (k : K))⁻¹ * (k : K)⁻¹ +
              J.conj
                (z.1.2 * (J.conj (k : K))⁻¹ * (k : K)⁻¹) +
              (z.1.1 * (k : K) * (J.conj (k : K))⁻¹ ^ 2) *
                J.conj
                  (z.1.1 * (k : K) * (J.conj (k : K))⁻¹ ^ 2) =
            (z.1.2 + J.conj z.1.2 + z.1.1 * J.conj z.1.1) *
              ((J.conj (k : K))⁻¹ * (k : K)⁻¹) := by
      rw [map_mul, map_mul, map_inv₀, J.conj_involutive,
        map_inv₀, map_mul, map_mul, map_pow, map_inv₀,
        J.conj_involutive]
      field_simp [hk, hconjk]
    dsimp [a', b']
    rw [hscale, z.2, zero_mul]
  let w : hermitianUnipotentCoord J := ⟨(a', b'), hparam⟩
  exact w

@[simp] public theorem hermitianTorusAction_fst
    {K : Type u} [Field K] (J : HermitianForm 3 K) (k : Kˣ)
    (z : hermitianUnipotentCoord J) :
    (hermitianTorusAction J k z).1.1 =
      z.1.1 * (k : K) * (J.conj (k : K))⁻¹ ^ 2 :=
  rfl

@[simp] public theorem hermitianTorusAction_snd
    {K : Type u} [Field K] (J : HermitianForm 3 K) (k : Kˣ)
    (z : hermitianUnipotentCoord J) :
    (hermitianTorusAction J k z).1.2 =
      z.1.2 * (J.conj (k : K))⁻¹ * (k : K)⁻¹ :=
  rfl

/-- The diagonal torus acts on the Heisenberg coordinates by the displayed
formula from Huppert II.10.12. -/
public theorem hermitianTorusGL_mul_unipotent
    {K : Type u} [Field K] (J : HermitianForm 3 K) (k : Kˣ)
    (z : hermitianUnipotentCoord J) :
    hermitianTorusGL J k * hermitianUnipotentGL J z =
      hermitianUnipotentGL J (hermitianTorusAction J k z) *
        hermitianTorusGL J k := by
  have hk : (k : K) ≠ 0 := Units.ne_zero k
  have hconjk : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change
    (hermitianTorusMatrix J k * hermitianUnipotentMatrix J z) i j =
      (hermitianUnipotentMatrix J (hermitianTorusAction J k z) *
        hermitianTorusMatrix J k) i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusMatrix, hermitianUnipotentMatrix,
      hermitianTorusAction,
      Matrix.mul_apply, Fin.sum_univ_three, map_mul, map_pow, map_inv₀]
  all_goals try rw [J.conj_involutive]
  all_goals field_simp [hk, hconjk]

@[expose] public def hermitianTorusSU
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Kˣ →* J.specialSubgroup :=
  { toFun := fun k => ⟨hermitianTorusGL J k, by
      apply (J.mem_specialSubgroup_iff (hermitianTorusGL J k)).mpr
      constructor
      · have hk : (k : K) ≠ 0 := Units.ne_zero k
        have hconjk : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk
        change J.conjTranspose (hermitianTorusMatrix J k) * J.form *
            hermitianTorusMatrix J k = J.form
        rw [hJstandard]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [hermitianTorusMatrix, HermitianForm.conjTranspose, Matrix.mul_apply,
            Fin.sum_univ_three, map_inv₀]
        all_goals rw [J.conj_involutive]
        · exact inv_mul_cancel₀ hk
        · calc
            (k : K) * (J.conj (k : K))⁻¹ *
                (J.conj (k : K) * (k : K)⁻¹) =
              ((k : K) * (k : K)⁻¹) *
                ((J.conj (k : K))⁻¹ * J.conj (k : K)) := by ring
            _ = 1 := by
              rw [mul_inv_cancel₀ hk, inv_mul_cancel₀ hconjk, one_mul]
      · ext
        change (hermitianTorusMatrix J k).det = 1
        have hk : (k : K) ≠ 0 := Units.ne_zero k
        have hconjk : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk
        simp [hermitianTorusMatrix, Matrix.det_fin_three, hk, hconjk]⟩
    map_one' := by
      apply Subtype.ext
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [hermitianTorusGL, hermitianTorusMatrix]
    map_mul' := by
      intro k l
      apply Subtype.ext
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j
      all_goals simp [hermitianTorusGL, hermitianTorusMatrix,
        Matrix.mul_apply, Fin.sum_univ_three, map_mul, mul_comm]
      all_goals ring }

/-- The diagonal torus homomorphism in the projective special unitary group. -/
@[expose] public def hermitianTorusPSU
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Kˣ →* ProjectiveSpecialUnitaryMatrixGroup J :=
  let f : Kˣ →* Matrix.ProjGenLinGroup (Fin 3) K :=
    Matrix.ProjGenLinGroup.mk.comp
      (J.specialSubgroup.subtype.comp (hermitianTorusSU J hJstandard))
  f.codRestrict (ProjectiveSpecialUnitaryMatrixGroup J) (fun k =>
    Subgroup.mem_map_of_mem Matrix.ProjGenLinGroup.mk
      (hermitianTorusSU J hJstandard k).property)

@[simp] public theorem hermitianTorusPSU_val
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (k : Kˣ) :
    ((hermitianTorusPSU J hJstandard k :
        ProjectiveSpecialUnitaryMatrixGroup J) :
      Matrix.ProjGenLinGroup (Fin 3) K) =
        Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k) :=
  rfl

/-- The exact torus/root commutation formula after projection to `PSU(3)`. -/
public theorem hermitianTorusPSU_mul_unipotent
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (k : Kˣ) (z : hermitianUnipotentCoord J) :
    hermitianTorusPSU J hJstandard k * hermitianUnipotentPSU J hJstandard z =
      hermitianUnipotentPSU J hJstandard (hermitianTorusAction J k z) *
        hermitianTorusPSU J hJstandard k := by
  apply Subtype.ext
  change Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k) *
      Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J z) =
    Matrix.ProjGenLinGroup.mk
        (hermitianUnipotentGL J (hermitianTorusAction J k z)) *
      Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k)
  rw [← map_mul, hermitianTorusGL_mul_unipotent, map_mul]

@[expose] public def hermitianWeylMatrix {K : Type u} [Field K] :
    Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 0, -1, 0; 1, 0, 0]

@[simp] public theorem hermitianWeylMatrix_eq
    {K : Type u} [Field K] :
    (hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) K) =
      !![0, 0, 1; 0, -1, 0; 1, 0, 0] :=
  rfl

@[expose] public def hermitianWeylGL {K : Type u} [Field K] : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero hermitianWeylMatrix (by
    simp [hermitianWeylMatrix, Matrix.det_fin_three])

@[expose] public def hermitianWeylSU
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    J.specialSubgroup :=
  ⟨hermitianWeylGL, by
    apply (J.mem_specialSubgroup_iff hermitianWeylGL).mpr
    constructor
    · change J.conjTranspose hermitianWeylMatrix * J.form *
          hermitianWeylMatrix = J.form
      rw [hJstandard]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hermitianWeylMatrix, HermitianForm.conjTranspose,
          Matrix.mul_apply, Fin.sum_univ_three]
    · ext
      change Matrix.det hermitianWeylMatrix = 1
      simp [hermitianWeylMatrix, Matrix.det_fin_three]⟩

/-- The Weyl element interchanging the two isotropic coordinate points in
`PSU(3)`. -/
@[expose] public def hermitianWeylPSU
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ProjectiveSpecialUnitaryMatrixGroup J :=
  ⟨Matrix.ProjGenLinGroup.mk hermitianWeylGL,
    Subgroup.mem_map_of_mem Matrix.ProjGenLinGroup.mk
      (hermitianWeylSU J hJstandard).property⟩

@[simp] public theorem hermitianWeylPSU_val
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ((hermitianWeylPSU J hJstandard :
        ProjectiveSpecialUnitaryMatrixGroup J) :
      Matrix.ProjGenLinGroup (Fin 3) K) =
        Matrix.ProjGenLinGroup.mk hermitianWeylGL :=
  rfl

/-- The left root coordinate in the rank-one Bruhat decomposition of a
noncentral Hermitian unipotent element. -/
@[expose] public def hermitianBruhatLeft
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (z : hermitianUnipotentCoord J) (hz : z.1.2 ≠ 0) :
    hermitianUnipotentCoord J :=
  ⟨(-z.1.1 / J.conj z.1.2, z.1.2⁻¹), by
    have hconjz : J.conj z.1.2 ≠ 0 := (map_ne_zero J.conj).2 hz
    dsimp only
    rw [map_inv₀, map_div₀, map_neg, J.conj_involutive]
    field_simp [hz, hconjz]
    linear_combination z.2⟩

/-- The right root coordinate in the rank-one Bruhat decomposition of a
noncentral Hermitian unipotent element. -/
@[expose] public def hermitianBruhatRight
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (z : hermitianUnipotentCoord J) (hz : z.1.2 ≠ 0) :
    hermitianUnipotentCoord J :=
  ⟨(-z.1.1 / z.1.2, z.1.2⁻¹), by
    have hconjz : J.conj z.1.2 ≠ 0 := (map_ne_zero J.conj).2 hz
    dsimp only
    rw [map_inv₀, map_div₀, map_neg]
    field_simp [hz, hconjz]
    linear_combination z.2⟩

/-- The explicit Bruhat decomposition used in Peterfalvi Chapter IV,
Section 3, Corollary 2. -/
public theorem hermitianWeylPSU_mul_unipotent_mul_weyl
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (z : hermitianUnipotentCoord J) (hz : z.1.2 ≠ 0) :
    hermitianWeylPSU J hJstandard *
          hermitianUnipotentPSU J hJstandard z *
        hermitianWeylPSU J hJstandard =
      hermitianUnipotentPSU J hJstandard (hermitianBruhatLeft J z hz) *
          hermitianTorusPSU J hJstandard (Units.mk0 z.1.2 hz) *
        hermitianWeylPSU J hJstandard *
      hermitianUnipotentPSU J hJstandard (hermitianBruhatRight J z hz) := by
  have hconjz : J.conj z.1.2 ≠ 0 := (map_ne_zero J.conj).2 hz
  have hGL :
      hermitianWeylGL (K := K) * hermitianUnipotentGL J z *
            hermitianWeylGL (K := K) =
        hermitianUnipotentGL J (hermitianBruhatLeft J z hz) *
            hermitianTorusGL J (Units.mk0 z.1.2 hz) *
          hermitianWeylGL (K := K) *
        hermitianUnipotentGL J (hermitianBruhatRight J z hz) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change
      ((hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) K) *
          hermitianUnipotentMatrix J z *
          (hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) K)) i j =
        (hermitianUnipotentMatrix J (hermitianBruhatLeft J z hz) *
          hermitianTorusMatrix J (Units.mk0 z.1.2 hz) *
          (hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) K) *
          hermitianUnipotentMatrix J (hermitianBruhatRight J z hz)) i j
    fin_cases i <;> fin_cases j <;>
      simp [hermitianWeylMatrix, hermitianUnipotentMatrix,
        hermitianTorusMatrix, hermitianBruhatLeft, hermitianBruhatRight,
        Matrix.mul_apply, Fin.sum_univ_three]
    all_goals field_simp [hz, hconjz]
    all_goals try rw [J.conj_involutive]
    all_goals try linear_combination z.1.2 * z.2
    all_goals try (ring_nf; done)
    simpa [add_comm, add_left_comm, add_assoc] using z.2.symm
  apply Subtype.ext
  change
    Matrix.ProjGenLinGroup.mk (hermitianWeylGL (K := K)) *
          Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J z) *
        Matrix.ProjGenLinGroup.mk (hermitianWeylGL (K := K)) =
      Matrix.ProjGenLinGroup.mk
            (hermitianUnipotentGL J (hermitianBruhatLeft J z hz)) *
          Matrix.ProjGenLinGroup.mk
            (hermitianTorusGL J (Units.mk0 z.1.2 hz)) *
        Matrix.ProjGenLinGroup.mk (hermitianWeylGL (K := K)) *
      Matrix.ProjGenLinGroup.mk
        (hermitianUnipotentGL J (hermitianBruhatRight J z hz))
  simpa only [map_mul] using congrArg Matrix.ProjGenLinGroup.mk hGL

/-- A nontrivial projective norm-one torus element.  The cube condition is
recorded explicitly because it is exactly what makes the Corollary 2 root
element noncentral. -/
public theorem exists_hermitian_norm_one_torus_cube_ne_one
    {K : Type u} [Field K] [Finite K]
    (J : HermitianForm 3 K) (q : ℕ)
    (hKcard : Nat.card K = q ^ 2)
    (hfixed_card : Nat.card {x : K // J.conj x = x} = q)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hq_gt : 2 < q) :
    ∃ k : Kˣ, (k : K) ^ (q + 1) = 1 ∧ (k : K) ^ 3 ≠ 1 ∧
      hermitianTorusPSU J hJstandard k ≠ 1 ∧
        J.conj (k : K) = (k : K)⁻¹ := by
  letI : IsCyclic Kˣ := inferInstance
  have hcardUnits : Nat.card Kˣ = q ^ 2 - 1 := by
    rw [Nat.card_units, hKcard]
  have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq q 1
  have hdq1 : q + 1 ∣ q ^ 2 - 1 := by
    rw [hfactor]
    exact dvd_mul_left (q + 1) (q - 1)
  have hnormRootsCard : Nat.card (rootsOfUnity (q + 1) K) = q + 1 := by
    rw [rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker,
      hcardUnits, Nat.gcd_eq_right hdq1]
  have hthree_lt : 3 < Nat.card (rootsOfUnity (q + 1) K) := by
    rw [hnormRootsCard]
    omega
  letI : IsCyclic (rootsOfUnity (q + 1) K) := inferInstance
  obtain ⟨k0, hkthree⟩ :=
    exists_pow_ne_one_of_isCyclic (G := rootsOfUnity (q + 1) K)
      (by decide : (3 : ℕ) ≠ 0) hthree_lt
  let k : Kˣ := (k0 : Kˣ)
  have hkqUnits : k ^ (q + 1) = 1 :=
    (mem_rootsOfUnity (q + 1) (k0 : Kˣ)).mp k0.property
  have hkq : (k : K) ^ (q + 1) = 1 := by
    simpa using congrArg Units.val hkqUnits
  have hk3 : (k : K) ^ 3 ≠ 1 := by
    intro h
    apply hkthree
    apply Subtype.ext
    apply Units.ext
    simpa [k] using h
  have hconjpow : J.conj (k : K) = (k : K) ^ q :=
    huppert_II_10_4_conj_eq_frobenius J q hKcard hfixed_card (k : K)
  have hnorm : J.conj (k : K) * (k : K) = 1 := by
    rw [hconjpow]
    simpa [pow_succ] using hkq
  have hconj : J.conj (k : K) = (k : K)⁻¹ :=
    eq_inv_of_mul_eq_one_left hnorm
  have htorus_ne : hermitianTorusPSU J hJstandard k ≠ 1 := by
    intro htorus
    have hpgl : Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k) = 1 :=
      congrArg Subtype.val htorus
    have hcenter : hermitianTorusGL J k ∈
        Subgroup.center (GL (Fin 3) K) := by
      rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
      exact hpgl
    rcases Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
      hcenter with ⟨c, hc⟩
    have h11 := congrArg
      (fun M : Matrix (Fin 3) (Fin 3) K => M 1 1) hc
    have h22 := congrArg
      (fun M : Matrix (Fin 3) (Fin 3) K => M 2 2) hc
    rw [hermitianTorusGL_val] at h11 h22
    simp [hermitianTorusMatrix, Matrix.scalar_apply] at h11 h22
    have hmid : J.conj (k : K) * (k : K)⁻¹ = (k : K) :=
      h11.symm.trans h22
    have hsq : J.conj (k : K) = (k : K) * (k : K) := by
      have h := congrArg (fun x : K => x * (k : K)) hmid
      simpa [mul_assoc, Units.ne_zero k] using h
    apply hk3
    calc
      (k : K) ^ 3 = ((k : K) * (k : K)) * (k : K) := by ring
      _ = J.conj (k : K) * (k : K) := by rw [← hsq]
      _ = 1 := hnorm
  exact ⟨k, hkq, hk3, htorus_ne, hconj⟩

/-- A Hermitian root element with nonzero second coordinate is nontrivial in
the projective unitary group. -/
public theorem hermitianUnipotentPSU_ne_one_of_snd_ne_zero
    {K : Type u} [Field K]
    (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (z : hermitianUnipotentCoord J) (hz : z.1.2 ≠ 0) :
    hermitianUnipotentPSU J hJstandard z ≠ 1 := by
  intro hroot
  have hpgl : Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J z) = 1 :=
    congrArg Subtype.val hroot
  have hcenter : hermitianUnipotentGL J z ∈
      Subgroup.center (GL (Fin 3) K) := by
    rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
    exact hpgl
  rcases Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
    hcenter with ⟨c, hc⟩
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 2) hc
  rw [hermitianUnipotentGL_val] at h02
  simp [hermitianUnipotentMatrix, Matrix.scalar_apply] at h02
  exact hz h02.symm

/-- A norm-one Hermitian torus element centralizes every involution in the
standard root subgroup. -/
public theorem hermitianTorusPSU_commute_unipotent_of_sq_eq_one
    {K : Type u} [Field K] [CharP K 2]
    (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (k : Kˣ) (hkconj : J.conj (k : K) = (k : K)⁻¹)
    (z : hermitianUnipotentCoord J)
    (hzsq : (hermitianUnipotentPSU J hJstandard z) ^ 2 = 1) :
    hermitianTorusPSU J hJstandard k *
        hermitianUnipotentPSU J hJstandard z =
      hermitianUnipotentPSU J hJstandard z *
        hermitianTorusPSU J hJstandard k := by
  have hzsq_root :
      hermitianUnipotentPSU J hJstandard (z ^ 2) = 1 := by
    simpa only [map_pow] using hzsq
  have hz_fst : z.1.1 = 0 := by
    by_contra hz_fst_ne
    apply hermitianUnipotentPSU_ne_one_of_snd_ne_zero
      J hJstandard (z ^ 2) at hzsq_root
    apply hzsq_root
    rw [pow_two]
    change z.1.2 + z.1.2 - z.1.1 * J.conj z.1.1 ≠ 0
    have htwo : (2 : K) = 0 := by
      simpa using CharP.cast_eq_zero K 2
    have hadd : z.1.2 + z.1.2 = 0 := by
      linear_combination z.1.2 * htwo
    rw [hadd, zero_sub]
    exact neg_ne_zero.mpr
      (mul_ne_zero hz_fst_ne ((map_ne_zero J.conj).2 hz_fst_ne))
  have haction : hermitianTorusAction J k z = z := by
    apply Subtype.ext
    apply Prod.ext
    · simp [hz_fst]
    · simp only [hermitianTorusAction_snd]
      rw [hkconj]
      field_simp [Units.ne_zero k]
  rw [hermitianTorusPSU_mul_unipotent J hJstandard k z, haction]

/-- A norm-one Hermitian torus element centralizes the standard Weyl element. -/
public theorem hermitianTorusPSU_commute_weyl_of_conj_eq_inv
    {K : Type u} [Field K]
    (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (k : Kˣ) (hkconj : J.conj (k : K) = (k : K)⁻¹) :
    hermitianTorusPSU J hJstandard k * hermitianWeylPSU J hJstandard =
      hermitianWeylPSU J hJstandard * hermitianTorusPSU J hJstandard k := by
  apply Subtype.ext
  change Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k) *
      Matrix.ProjGenLinGroup.mk (hermitianWeylGL (K := K)) =
    Matrix.ProjGenLinGroup.mk (hermitianWeylGL (K := K)) *
      Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k)
  rw [← map_mul, ← map_mul]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusGL, hermitianTorusMatrix, hermitianWeylGL,
      hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three, hkconj]

/-- In characteristic two, the right Bruhat root is the inverse root conjugated
by the norm-one torus element whose cube is the second root coordinate. -/
public theorem hermitianBruhatRight_eq_torus_conjugate
    {K : Type u} [Field K] [CharP K 2]
    (J : HermitianForm 3 K)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (k : Kˣ) (hkconj : J.conj (k : K) = (k : K)⁻¹)
    (z : hermitianUnipotentCoord J) (hz : z.1.2 ≠ 0)
    (hz2 : z.1.2 = (k : K) ^ 3) :
    hermitianUnipotentPSU J hJstandard (hermitianBruhatRight J z hz) =
      (hermitianTorusPSU J hJstandard k)⁻¹ *
        (hermitianUnipotentPSU J hJstandard z)⁻¹ *
          hermitianTorusPSU J hJstandard k := by
  have hcoord : hermitianBruhatRight J z hz =
      hermitianTorusAction J k⁻¹ z⁻¹ := by
    apply Subtype.ext
    apply Prod.ext
    · simp only [hermitianBruhatRight, hermitianTorusAction_fst,
        Units.val_inv_eq_inv_val]
      change -z.1.1 / z.1.2 =
        -z.1.1 * (k : K)⁻¹ * (J.conj ((k : K)⁻¹))⁻¹ ^ 2
      rw [map_inv₀, hkconj, hz2]
      field_simp [Units.ne_zero k]
    · simp only [hermitianBruhatRight, hermitianTorusAction_snd,
        Units.val_inv_eq_inv_val]
      change z.1.2⁻¹ =
        J.conj z.1.2 * (J.conj ((k : K)⁻¹))⁻¹ * ((k : K)⁻¹)⁻¹
      rw [map_inv₀, hkconj, hz2]
      field_simp [Units.ne_zero k]
      rw [map_pow, hkconj]
      field_simp [Units.ne_zero k]
  let rootPSU := hermitianUnipotentPSU J hJstandard
  let torusPSU := hermitianTorusPSU J hJstandard
  have htorusRoot := hermitianTorusPSU_mul_unipotent J hJstandard k⁻¹ z⁻¹
  calc
    rootPSU (hermitianBruhatRight J z hz) =
        rootPSU (hermitianTorusAction J k⁻¹ z⁻¹) := congrArg rootPSU hcoord
    _ = (rootPSU (hermitianTorusAction J k⁻¹ z⁻¹) * torusPSU k⁻¹) *
          torusPSU k := by simp
    _ = (torusPSU k⁻¹ * rootPSU z⁻¹) * torusPSU k := by
      rw [← htorusRoot]
    _ = (torusPSU k)⁻¹ * (rootPSU z)⁻¹ * torusPSU k := by
      rw [map_inv, map_inv]

/-- The explicit PSU seed used in Peterfalvi Chapter IV, Section 3,
Corollary 2.  Both outer factors are standard root elements, while the middle
factor is a nontrivial norm-one torus element centralizing the Weyl element. -/
public theorem exists_hermitianPSU_corollary_two_seed
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (q : ℕ)
    (hKcard : Nat.card K = q ^ 2)
    (hfixedCard : Nat.card {x : K // J.conj x = x} = q)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hq_gt : 2 < q) :
    ∃ omega gamma zeta : ProjectiveSpecialUnitaryMatrixGroup J,
      omega ^ 2 ≠ 1 ∧ zeta ≠ 1 ∧
        zeta * hermitianWeylPSU J hJstandard =
          hermitianWeylPSU J hJstandard * zeta ∧
        hermitianWeylPSU J hJstandard * omega *
              hermitianWeylPSU J hJstandard =
          gamma * zeta ^ 3 * hermitianWeylPSU J hJstandard *
            (zeta⁻¹ * omega⁻¹ * zeta) ∧
        (∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
          (∃ z : hermitianUnipotentCoord J,
            x = hermitianUnipotentPSU J hJstandard z) →
          x ^ 2 = 1 → zeta * x = x * zeta) ∧
        (∃ z : hermitianUnipotentCoord J,
          omega = hermitianUnipotentPSU J hJstandard z) ∧
        (∃ z : hermitianUnipotentCoord J,
          gamma = hermitianUnipotentPSU J hJstandard z) ∧
        ∃ k : Kˣ, zeta = hermitianTorusPSU J hJstandard k := by
  obtain ⟨k, _hkq, hk3, hk_ne, hkconj⟩ :=
    exists_hermitian_norm_one_torus_cube_ne_one
      J q hKcard hfixedCard hJstandard hq_gt
  let y : Kˣ := k ^ 3
  have hy_ne : (y : K) ≠ 1 := by
    simpa [y] using hk3
  have hy_conj : J.conj (y : K) = (y : K)⁻¹ := by
    simp [y, map_pow, hkconj]
  have hy_norm : J.conj (y : K) * (y : K) = 1 := by
    rw [hy_conj]
    exact inv_mul_cancel₀ (Units.ne_zero y)
  let target : K := -((y : K) + J.conj (y : K))
  have htarget_fixed : J.conj target = target := by
    dsimp [target]
    rw [map_neg, map_add, J.conj_involutive]
    ring
  have hneg (a : K) : -a = a := by
    have htwo : (2 : K) = 0 := by
      simpa using (CharP.cast_eq_zero K 2)
    calc
      -a = -a + (2 : K) * a := by rw [htwo, zero_mul, add_zero]
      _ = a := by ring
  have htarget_ne : target ≠ 0 := by
    intro ht
    have hsum : (y : K) + J.conj (y : K) = 0 := neg_eq_zero.mp ht
    have hy_fixed : (y : K) = J.conj (y : K) := by
      calc
        (y : K) = -J.conj (y : K) := eq_neg_of_add_eq_zero_left hsum
        _ = J.conj (y : K) := hneg _
    have hy_sq : (y : K) ^ 2 = 1 := by
      calc
        (y : K) ^ 2 = (y : K) * (y : K) := by ring
        _ = J.conj (y : K) * (y : K) :=
          congrArg (fun a : K => a * (y : K)) hy_fixed
        _ = 1 := hy_norm
    rcases sq_eq_one_iff.mp hy_sq with hy_one | hy_neg_one
    · exact hy_ne hy_one
    · exact hy_ne (hy_neg_one.trans (hneg 1))
  obtain ⟨x, hx_ne, hxnorm⟩ :=
    huppert_II_10_4_norm_surjective
      J q hKcard hfixedCard target htarget_fixed htarget_ne
  let z : hermitianUnipotentCoord J :=
    ⟨(x, (y : K)), by
      dsimp only
      dsimp [target] at hxnorm
      linear_combination hxnorm⟩
  have hz_snd : z.1.2 = (k : K) ^ 3 := by rfl
  have hz_ne : z.1.2 ≠ 0 := Units.ne_zero y
  have htwo : (2 : K) = 0 := by
    simpa using (CharP.cast_eq_zero K 2)
  have hzsq_snd : ((z ^ 2 : hermitianUnipotentCoord J) : K × K).2 = target := by
    rw [pow_two]
    change (y : K) + (y : K) - x * J.conj x = target
    rw [show (y : K) + (y : K) = 0 by
      linear_combination (y : K) * htwo, zero_sub, hneg]
    exact hxnorm
  let omega := hermitianUnipotentPSU J hJstandard z
  let gamma :=
    hermitianUnipotentPSU J hJstandard (hermitianBruhatLeft J z hz_ne)
  let zeta := hermitianTorusPSU J hJstandard k
  have homega_sq : omega ^ 2 ≠ 1 := by
    dsimp [omega]
    rw [← map_pow]
    apply hermitianUnipotentPSU_ne_one_of_snd_ne_zero
    rw [hzsq_snd]
    exact htarget_ne
  have hcomm : zeta * hermitianWeylPSU J hJstandard =
      hermitianWeylPSU J hJstandard * zeta :=
    hermitianTorusPSU_commute_weyl_of_conj_eq_inv
      J hJstandard k hkconj
  have hright :
      hermitianUnipotentPSU J hJstandard (hermitianBruhatRight J z hz_ne) =
        zeta⁻¹ * omega⁻¹ * zeta := by
    exact hermitianBruhatRight_eq_torus_conjugate
      J hJstandard k hkconj z hz_ne hz_snd
  refine ⟨omega, gamma, zeta, homega_sq, hk_ne, hcomm, ?_, ?_, ⟨z, rfl⟩,
    ⟨hermitianBruhatLeft J z hz_ne, rfl⟩, ⟨k, rfl⟩⟩
  · rw [hermitianWeylPSU_mul_unipotent_mul_weyl J hJstandard z hz_ne]
    have hy_units : Units.mk0 z.1.2 hz_ne = k ^ 3 := by
      apply Units.ext
      rfl
    rw [hy_units, map_pow, hright]
  · intro x hxroot hxsq
    rcases hxroot with ⟨w, rfl⟩
    exact hermitianTorusPSU_commute_unipotent_of_sq_eq_one
      J hJstandard k hkconj w hxsq

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Huppert II.10.12, the natural `PSU(3,q^2)` action and point stabilizer. -/
public theorem huppert_II_10_12
    {K : Type u} [Field K] [Finite K]
    (J : HermitianForm 3 K) (q : ℕ)
    (hKcard : Nat.card K = q ^ 2)
    (hfixed_card : Nat.card {x : K // J.conj x = x} = q)
    (hJstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    let P := ℙ K (Fin 3 → K)
    let A : Set P :=
      {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
        x = Projectivization.mk K v hv ∧
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
    let Omega := {x : P // x ∈ A}
    let G := ProjectiveSpecialUnitaryMatrixGroup J
    Nat.card Omega = q ^ 3 + 1 ∧
    ∃ (rho : G →* Equiv.Perm Omega) (pinf : Omega),
      Function.Injective rho ∧
      (∀ g : G, ∀ z : Omega, ∀ M : J.specialSubgroup,
        Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) K) =
            (g : Matrix.ProjGenLinGroup (Fin 3) K) →
          ((rho g z : Omega) : P) =
            (Matrix.GeneralLinearGroup.toLin
              (M : GL (Fin 3) K)).toLinearEquiv • (z : P)) ∧
      let U : Subgroup G :=
        (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho
      Nat.card U = q ^ 3 * (q ^ 2 - 1) / Nat.gcd (q + 1) 3 ∧
      (∃ (R H : Subgroup G),
        R ≤ U ∧ H ≤ U ∧ U ≤ Subgroup.normalizer R ∧
        R ⊓ H = ⊥ ∧ R ⊔ H = U ∧ IsCyclic H ∧
        Nat.card R = q ^ 3 ∧
        commutator R = Subgroup.center R ∧
        Nat.card (commutator R) = q ∧
        Nat.card H = (q ^ 2 - 1) / Nat.gcd (q + 1) 3 ∧
        (∀ a b : Omega, a ≠ pinf → b ≠ pinf →
          ∃! r : R, rho (r : G) a = b) ∧
        (∃ coordR :
            {z : K × K // z.2 + J.conj z.2 + z.1 * J.conj z.1 = 0} ≃ R,
          ∀ z : {z : K × K //
              z.2 + J.conj z.2 + z.1 * J.conj z.1 = 0},
            ∃ M : GL (Fin 3) K,
              (M : Matrix (Fin 3) (Fin 3) K) =
                !![1, (z : K × K).1, (z : K × K).2;
                   0, 1, -J.conj (z : K × K).1;
                   0, 0, 1] ∧
              ((((coordR z : R) : G) :
                Matrix.ProjGenLinGroup (Fin 3) K)) =
                  Matrix.ProjGenLinGroup.mk M) ∧
        (∀ h : H,
          ∃ k : Kˣ, ∃ M : GL (Fin 3) K,
            (M : Matrix (Fin 3) (Fin 3) K) =
              !![(J.conj (k : K))⁻¹, 0, 0;
                 0, J.conj (k : K) * (k : K)⁻¹, 0;
                 0, 0, (k : K)] ∧
            ((((h : H) : G) : Matrix.ProjGenLinGroup (Fin 3) K)) =
              Matrix.ProjGenLinGroup.mk M) ∧
        (∀ k : Kˣ,
          ∃ h : H, ∃ M : GL (Fin 3) K,
            (M : Matrix (Fin 3) (Fin 3) K) =
              !![(J.conj (k : K))⁻¹, 0, 0;
                 0, J.conj (k : K) * (k : K)⁻¹, 0;
                 0, 0, (k : K)] ∧
            ((((h : H) : G) : Matrix.ProjGenLinGroup (Fin 3) K)) =
              Matrix.ProjGenLinGroup.mk M)) ∧
      (∀ a b c d : Omega, a ≠ b → c ≠ d →
        ∃ g : G, rho g a = c ∧ rho g b = d) ∧
      Nat.card G =
        (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) ∧
      (2 < q →
        ∃ g : G, g ≠ 1 ∧
          ∃ a b c : Omega,
            a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
              rho g a = a ∧ rho g b = b ∧ rho g c = c) := by
  let P := ℙ K (Fin 3 → K)
  let A : Set P :=
    {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
      x = Projectivization.mk K v hv ∧
        dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Omega := {x : P // x ∈ A}
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  change Nat.card Omega = q ^ 3 + 1 ∧
    ∃ (rho : G →* Equiv.Perm Omega) (pinf : Omega),
      Function.Injective rho ∧
      (∀ g : G, ∀ z : Omega, ∀ M : J.specialSubgroup,
        Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) K) =
            (g : Matrix.ProjGenLinGroup (Fin 3) K) →
          ((rho g z : Omega) : P) =
            (Matrix.GeneralLinearGroup.toLin
              (M : GL (Fin 3) K)).toLinearEquiv • (z : P)) ∧
      let U : Subgroup G :=
        (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho
      Nat.card U = q ^ 3 * (q ^ 2 - 1) / Nat.gcd (q + 1) 3 ∧
      (∃ (R H : Subgroup G),
        R ≤ U ∧ H ≤ U ∧ U ≤ Subgroup.normalizer R ∧
        R ⊓ H = ⊥ ∧ R ⊔ H = U ∧ IsCyclic H ∧
        Nat.card R = q ^ 3 ∧
        commutator R = Subgroup.center R ∧
        Nat.card (commutator R) = q ∧
        Nat.card H = (q ^ 2 - 1) / Nat.gcd (q + 1) 3 ∧
        (∀ a b : Omega, a ≠ pinf → b ≠ pinf →
          ∃! r : R, rho (r : G) a = b) ∧
        (∃ coordR :
            {z : K × K // z.2 + J.conj z.2 + z.1 * J.conj z.1 = 0} ≃ R,
          ∀ z : {z : K × K //
              z.2 + J.conj z.2 + z.1 * J.conj z.1 = 0},
            ∃ M : GL (Fin 3) K,
              (M : Matrix (Fin 3) (Fin 3) K) =
                !![1, (z : K × K).1, (z : K × K).2;
                   0, 1, -J.conj (z : K × K).1;
                   0, 0, 1] ∧
              ((((coordR z : R) : G) :
                Matrix.ProjGenLinGroup (Fin 3) K)) =
                  Matrix.ProjGenLinGroup.mk M) ∧
        (∀ h : H,
          ∃ k : Kˣ, ∃ M : GL (Fin 3) K,
            (M : Matrix (Fin 3) (Fin 3) K) =
              !![(J.conj (k : K))⁻¹, 0, 0;
                 0, J.conj (k : K) * (k : K)⁻¹, 0;
                 0, 0, (k : K)] ∧
            ((((h : H) : G) : Matrix.ProjGenLinGroup (Fin 3) K)) =
              Matrix.ProjGenLinGroup.mk M) ∧
        (∀ k : Kˣ,
          ∃ h : H, ∃ M : GL (Fin 3) K,
            (M : Matrix (Fin 3) (Fin 3) K) =
              !![(J.conj (k : K))⁻¹, 0, 0;
                 0, J.conj (k : K) * (k : K)⁻¹, 0;
                 0, 0, (k : K)] ∧
            ((((h : H) : G) : Matrix.ProjGenLinGroup (Fin 3) K)) =
              Matrix.ProjGenLinGroup.mk M)) ∧
      (∀ a b c d : Omega, a ≠ b → c ≠ d →
        ∃ g : G, rho g a = c ∧ rho g b = d) ∧
      Nat.card G =
        (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) ∧
      (2 < q →
        ∃ g : G, g ≠ 1 ∧
          ∃ a b c : Omega,
            a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
              rho g a = a ∧ rho g b = b ∧ rho g c = c)
  let S := {z : K × K //
    z.2 + J.conj z.2 + z.1 * J.conj z.1 = 0}
  let vinf : Fin 3 → K := ![1, 0, 0]
  have hvinf : vinf ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h 0)
  have hiso_infinity :
      dotProduct (fun i => J.conj (vinf i)) (J.form.mulVec vinf) = 0 := by
    rw [hJstandard]
    simp [vinf, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  let pinf : Omega :=
    ⟨Projectivization.mk K vinf hvinf,
      ⟨vinf, hvinf, rfl, hiso_infinity⟩⟩
  let vaff (z : S) : Fin 3 → K := ![z.1.2, z.1.1, 1]
  have hvaff (z : S) : vaff z ≠ 0 := by
    intro h
    have h2 := congrFun h (2 : Fin 3)
    simp only [vaff, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, Pi.zero_apply] at h2
    exact one_ne_zero h2
  have hpointData :
      Nat.card S = q ^ 3 ∧
        Nat.card {b : K // b + J.conj b = 0} = q ∧
        ∃ e : Omega ≃ Option S,
          e pinf = none ∧
          ∀ z : S,
            ((e.symm (some z) : Omega) : P) =
              Projectivization.mk K (vaff z) (hvaff z) := by
    classical
    letI : Fintype K := Fintype.ofFinite K
    have h1012_trace_fiber_card (a : K) :
        Nat.card {b : K //
          b + J.conj b + a * J.conj a = 0} = q := by
      let k0 := FixedBy.subfield K J.conj
      have hk0card : Nat.card k0 = q := by
        simpa [k0, FixedBy.subfield, RingAut.smul_def] using hfixed_card
      have hq : 0 < q := by
        rw [← hk0card]
        exact Nat.card_pos
      have hfinrank : Module.finrank k0 K = 2 :=
        huppert_II_10_4_fixedField_finrank_two J q hKcard hfixed_card
      letI : Fintype k0 := Fintype.ofFinite k0
      have hpow : ∀ x : K, x ^ q = J.conj x := fun x =>
        (huppert_II_10_4_conj_eq_frobenius
          J q hKcard hfixed_card x).symm
      let tr : K →ₗ[k0] k0 := Algebra.trace k0 K
      have htrace_formula (b : K) :
          algebraMap k0 K (tr b) = b + J.conj b := by
        change algebraMap k0 K (Algebra.trace k0 K b) = _
        rw [FiniteField.algebraMap_trace_eq_sum_pow]
        erw [hfinrank]
        simp [Finset.sum_range_succ, -Nat.card_eq_fintype_card, hk0card, hpow]
      have hsurj : Function.Surjective tr :=
        Algebra.trace_surjective k0 K
      have hrange : tr.toAddMonoidHom.range = ⊤ :=
        AddMonoidHom.range_eq_top.mpr hsurj
      have hindex : tr.toAddMonoidHom.ker.index = Nat.card k0 := by
        rw [AddSubgroup.index_ker, hrange]
        simp
      have hmul := tr.toAddMonoidHom.ker.card_mul_index
      rw [hindex, hk0card, hKcard] at hmul
      have htrker_card : Nat.card tr.toAddMonoidHom.ker = q := by
        nlinarith
      let T : K →+ K :=
        { toFun := fun b => b + J.conj b
          map_zero' := by simp
          map_add' := by
            intro x y
            simp only [map_add]
            abel }
      have hker : T.ker = tr.toAddMonoidHom.ker := by
        ext b
        constructor
        · intro hb
          change tr b = 0
          apply (FaithfulSMul.algebraMap_injective k0 K)
          rw [map_zero, htrace_formula]
          exact hb
        · intro hb
          change tr b = 0 at hb
          change T b = 0
          change b + J.conj b = 0
          rw [← htrace_formula, hb, map_zero]
      have hTker_card : Nat.card T.ker = q := by
        rw [hker, htrker_card]
      let c : K := -(a * J.conj a)
      have hc_fixed : J.conj c = c := by
        dsimp [c]
        rw [map_neg, map_mul, J.conj_involutive]
        ring
      let c0 : k0 := ⟨c, by
        simpa [k0, FixedBy.subfield, RingAut.smul_def] using hc_fixed⟩
      obtain ⟨b0, hb0⟩ := hsurj c0
      have hTb0 : T b0 = c := by
        change b0 + J.conj b0 = c
        rw [← htrace_formula, hb0]
        rfl
      let e :
          {b : K // b + J.conj b + a * J.conj a = 0} ≃ T.ker :=
        { toFun := fun b => ⟨b.1 - b0, by
              change T (b.1 - b0) = 0
              rw [map_sub, hTb0]
              have hb : T b.1 = c := by
                change b.1 + J.conj b.1 = -(a * J.conj a)
                rw [eq_neg_iff_add_eq_zero]
                exact b.2
              rw [hb, sub_self]⟩
          invFun := fun x => ⟨x.1 + b0, by
              have hx : T (x.1 + b0) = c := by
                rw [map_add, x.2, hTb0, zero_add]
              change
                (x.1 + b0) + J.conj (x.1 + b0) + a * J.conj a = 0
              change T (x.1 + b0) + a * J.conj a = 0
              rw [hx]
              simp [c]⟩
          left_inv := by
            intro b
            apply Subtype.ext
            simp
          right_inv := by
            intro x
            apply Subtype.ext
            simp }
      calc
        Nat.card {b : K // b + J.conj b + a * J.conj a = 0} =
            Nat.card T.ker := Nat.card_congr e
        _ = q := hTker_card
    have hScard : Nat.card S = q ^ 3 := by
      let e : S ≃ Σ a : K,
          {b : K // b + J.conj b + a * J.conj a = 0} :=
        { toFun := fun z => ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
          invFun := fun z => ⟨(z.1, z.2.1), z.2.2⟩
          left_inv := by intro z; rfl
          right_inv := by intro z; rfl }
      calc
        Nat.card S = Nat.card (Σ a : K,
            {b : K // b + J.conj b + a * J.conj a = 0}) :=
          Nat.card_congr e
        _ = ∑ a : K,
            Nat.card {b : K //
              b + J.conj b + a * J.conj a = 0} := Nat.card_sigma
        _ = ∑ _a : K, q := by
          apply Finset.sum_congr rfl
          intro a _
          exact h1012_trace_fiber_card a
        _ = Nat.card K * q := by
          rw [Nat.card_eq_fintype_card]
          simp
        _ = q ^ 2 * q := by rw [hKcard]
        _ = q ^ 3 := by ring
    have h1012_isotropic_coordinate_equiv :
        ∃ e : Omega ≃ Option S,
          e pinf = none ∧
          ∀ z : S,
            ((e.symm (some z) : Omega) : P) =
              Projectivization.mk K (vaff z) (hvaff z) := by
      have hiso_formula (v : Fin 3 → K) :
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) =
            J.conj (v 0) * v 2 + J.conj (v 1) * v 1 +
              J.conj (v 2) * v 0 := by
        rw [hJstandard]
        simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      have hiso_affine (z : S) :
          dotProduct (fun i => J.conj (vaff z i))
              (J.form.mulVec (vaff z)) = 0 := by
        rw [hiso_formula]
        simpa [vaff, add_comm, add_left_comm, add_assoc, mul_comm] using z.2
      let paff (z : S) : Omega :=
        ⟨Projectivization.mk K (vaff z) (hvaff z),
          ⟨vaff z, hvaff z, rfl, hiso_affine z⟩⟩
      let ofOption : Option S → Omega
        | none => pinf
        | some z => paff z
      have hofOption_injective : Function.Injective ofOption := by
        intro z w hzw
        cases z with
        | none =>
            cases w with
            | none => rfl
            | some w =>
                exfalso
                have hp : Projectivization.mk K vinf hvinf =
                    Projectivization.mk K (vaff w) (hvaff w) :=
                  congrArg Subtype.val hzw
                rcases (Projectivization.mk_eq_mk_iff'
                  K vinf (vaff w) hvinf (hvaff w)).mp hp with ⟨c, hc⟩
                have hc0 := congrFun hc (0 : Fin 3)
                have hc2 := congrFun hc (2 : Fin 3)
                have hc_zero : c = 0 := by
                  simpa [vinf, vaff] using hc2
                subst c
                simp [vinf, vaff] at hc0

        | some z =>
            cases w with
            | none =>
                exfalso
                have hp : Projectivization.mk K (vaff z) (hvaff z) =
                    Projectivization.mk K vinf hvinf :=
                  congrArg Subtype.val hzw
                rcases (Projectivization.mk_eq_mk_iff'
                  K (vaff z) vinf (hvaff z) hvinf).mp hp with ⟨c, hc⟩
                have hc2 := congrFun hc (2 : Fin 3)
                simp [vinf, vaff] at hc2
            | some w =>
                congr 1
                apply Subtype.ext
                apply Prod.ext
                · have hp : Projectivization.mk K (vaff z) (hvaff z) =
                      Projectivization.mk K (vaff w) (hvaff w) :=
                    congrArg Subtype.val hzw
                  rcases (Projectivization.mk_eq_mk_iff'
                    K (vaff z) (vaff w) (hvaff z) (hvaff w)).mp hp with
                    ⟨c, hc⟩
                  have hc2 := congrFun hc (2 : Fin 3)
                  have hc1 := congrFun hc (1 : Fin 3)
                  have hc_one : c = 1 := by
                    simpa [vaff] using hc2
                  subst c
                  simpa [vaff] using hc1.symm
                · have hp : Projectivization.mk K (vaff z) (hvaff z) =
                      Projectivization.mk K (vaff w) (hvaff w) :=
                    congrArg Subtype.val hzw
                  rcases (Projectivization.mk_eq_mk_iff'
                    K (vaff z) (vaff w) (hvaff z) (hvaff w)).mp hp with
                    ⟨c, hc⟩
                  have hc2 := congrFun hc (2 : Fin 3)
                  have hc0 := congrFun hc (0 : Fin 3)
                  have hc_one : c = 1 := by
                    simpa [vaff] using hc2
                  subst c
                  simpa [vaff] using hc0.symm
      have hofOption_surjective : Function.Surjective ofOption := by
        intro x
        rcases x.2 with ⟨v, hv, hx, hiso⟩
        rw [hiso_formula] at hiso
        by_cases hv2 : v 2 = 0
        · have hv1 : v 1 = 0 := by
            have hprod : J.conj (v 1) * v 1 = 0 := by
              simpa [hv2] using hiso
            by_contra hv1
            exact (mul_ne_zero ((map_ne_zero J.conj).2 hv1) hv1) hprod
          have hv0 : v 0 ≠ 0 := by
            intro hv0
            apply hv
            funext i
            fin_cases i <;> simp [hv0, hv1, hv2]
          refine ⟨none, ?_⟩
          apply Subtype.ext
          change Projectivization.mk K vinf hvinf = x.1
          rw [hx]
          apply (Projectivization.mk_eq_mk_iff'
            K vinf v hvinf hv).mpr
          refine ⟨(v 0)⁻¹, ?_⟩
          funext i
          fin_cases i <;> simp [vinf, hv0, hv1, hv2]
        · have hz :
              v 0 / v 2 + J.conj (v 0 / v 2) +
                (v 1 / v 2) * J.conj (v 1 / v 2) = 0 := by
            have hconjv2 : J.conj (v 2) ≠ 0 :=
              (map_ne_zero J.conj).2 hv2
            rw [map_div₀, map_div₀]
            field_simp [hv2, hconjv2]
            linear_combination hiso
          let z : S := ⟨(v 1 / v 2, v 0 / v 2), hz⟩
          refine ⟨some z, ?_⟩
          apply Subtype.ext
          change Projectivization.mk K (vaff z) (hvaff z) = x.1
          rw [hx]
          apply (Projectivization.mk_eq_mk_iff'
            K (vaff z) v (hvaff z) hv).mpr
          refine ⟨(v 2)⁻¹, ?_⟩
          funext i
          fin_cases i <;> simp [vaff, z, hv2, div_eq_inv_mul]
      let e := (Equiv.ofBijective ofOption
        ⟨hofOption_injective, hofOption_surjective⟩).symm
      refine ⟨e, ?_, ?_⟩
      · apply (Equiv.symm_apply_eq (Equiv.ofBijective ofOption
          ⟨hofOption_injective, hofOption_surjective⟩)).mpr
        rfl
      · intro z
        rfl
    have htraceZeroCard :
        Nat.card {b : K // b + J.conj b = 0} = q := by
      simpa using h1012_trace_fiber_card (0 : K)
    exact ⟨hScard, htraceZeroCard, h1012_isotropic_coordinate_equiv⟩
  rcases hpointData with ⟨hScard, htraceZeroCard, hOmegaEquiv⟩
  have hpoints : Nat.card Omega = q ^ 3 + 1 := by
    calc
      Nat.card Omega = Nat.card (Option S) :=
        Nat.card_congr hOmegaEquiv.choose
      _ = Nat.card S + 1 := Finite.card_option
      _ = q ^ 3 + 1 := by rw [hScard]
  have haction :
      ∃ rho : G →* Equiv.Perm Omega,
        Function.Injective rho ∧
        (∀ g : G, ∀ z : Omega, ∀ M : J.specialSubgroup,
          Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) K) =
              (g : Matrix.ProjGenLinGroup (Fin 3) K) →
            ((rho g z : Omega) : P) =
              (Matrix.GeneralLinearGroup.toLin
                (M : GL (Fin 3) K)).toLinearEquiv • (z : P)) := by
    classical
    letI : MulAction (GL (Fin 3) K) P :=
      MulAction.compHom P Matrix.GeneralLinearGroup.toLin.toMonoidHom
    have hscalar (u : Kˣ) (x : P) :
        Matrix.GeneralLinearGroup.scalar (Fin 3) u • x = x := by
      induction x using Projectivization.ind with
      | h v hv =>
          change Matrix.GeneralLinearGroup.toLin
            (Matrix.GeneralLinearGroup.scalar (Fin 3) u) •
              Projectivization.mk K v hv = _
          rw [Projectivization.smul_mk]
          apply (Projectivization.mk_eq_mk_iff'
            K _ _ _ _).mpr
          refine ⟨(u : K), ?_⟩
          change (u : K) • v = Matrix.mulVecLin
            (Matrix.GeneralLinearGroup.scalar (Fin 3) u) v
          ext i
          simp [Matrix.GeneralLinearGroup.scalar, Matrix.mulVecLin,
            Matrix.mulVec_diagonal]
    letI : MulAction (Matrix.ProjGenLinGroup (Fin 3) K) P :=
      Matrix.ProjGenLinGroup.mulActionOfGL hscalar
    have h1012_unitary_preserves_isotropic
        (M : J.specialSubgroup) (v : Fin 3 → K) :
        let Mmat := ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        dotProduct (fun i => J.conj (Mmat.mulVec v i))
            (J.form.mulVec (Mmat.mulVec v)) =
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) := by
      exact hermitian_unitary_preserves_self_pairing J
        ⟨(M : GL (Fin 3) K),
          J.specialSubgroup_le_unitarySubgroup M.property⟩ v
    have hA_smul (g : G) {x : P} (hxA : x ∈ A) :
        (g : Matrix.ProjGenLinGroup (Fin 3) K) • x ∈ A := by
      rcases g.property with ⟨M, hM, hMg⟩
      let Mu : J.specialSubgroup := ⟨M, hM⟩
      let Mmat := (M : Matrix (Fin 3) (Fin 3) K)
      rcases hxA with ⟨v, hv, hx, hiso⟩
      have hMv : Mmat.mulVec v ≠ 0 := by
        intro hzero
        apply hv
        exact (Matrix.mulVec_injective_of_isUnit (Units.isUnit M))
          (by simpa using hzero)
      refine ⟨Mmat.mulVec v, hMv, ?_, ?_⟩
      · rw [hx, ← hMg]
        rw [Matrix.ProjGenLinGroup.mk_smul hscalar]
        change Matrix.GeneralLinearGroup.toLin M •
            Projectivization.mk K v hv = _
        rw [Projectivization.smul_mk]
        rfl
      · rw [h1012_unitary_preserves_isotropic Mu v]
        exact hiso
    let smulOmega (g : G) (z : Omega) : Omega :=
      ⟨(g : Matrix.ProjGenLinGroup (Fin 3) K) • (z : P), hA_smul g z.2⟩
    letI : SMul G Omega := ⟨smulOmega⟩
    letI : MulAction G Omega :=
      { one_smul := by
          intro z
          apply Subtype.ext
          exact one_smul _ _
        mul_smul := by
          intro g h z
          apply Subtype.ext
          exact mul_smul (g : Matrix.ProjGenLinGroup (Fin 3) K)
            (h : Matrix.ProjGenLinGroup (Fin 3) K) (z : P) }
    let rho : G →* Equiv.Perm Omega := MulAction.toPermHom G Omega
    have h1012_curve_action_faithful : Function.Injective rho := by
      let k0 := FixedBy.subfield K J.conj
      have hk0card : Nat.card k0 = q := by
        simpa [k0, FixedBy.subfield, RingAut.smul_def] using hfixed_card
      have hq : 1 < q := by
        rw [← hk0card]
        exact Finite.one_lt_card
      have hfinrank : Module.finrank k0 K = 2 :=
        huppert_II_10_4_fixedField_finrank_two J q hKcard hfixed_card
      letI : Fintype k0 := Fintype.ofFinite k0
      have hpow : ∀ x : K, x ^ q = J.conj x := fun x =>
        (huppert_II_10_4_conj_eq_frobenius
          J q hKcard hfixed_card x).symm
      let tr : K →ₗ[k0] k0 := Algebra.trace k0 K
      have htrace_formula (x : K) :
          algebraMap k0 K (tr x) = x + J.conj x := by
        change algebraMap k0 K (Algebra.trace k0 K x) = _
        rw [FiniteField.algebraMap_trace_eq_sum_pow]
        erw [hfinrank]
        simp [Finset.sum_range_succ, -Nat.card_eq_fintype_card,
          hk0card, hpow]
      have hsurj : Function.Surjective tr :=
        Algebra.trace_surjective k0 K
      have hrange : tr.toAddMonoidHom.range = ⊤ :=
        AddMonoidHom.range_eq_top.mpr hsurj
      have hindex : tr.toAddMonoidHom.ker.index = Nat.card k0 := by
        rw [AddSubgroup.index_ker, hrange]
        simp
      have hmul := tr.toAddMonoidHom.ker.card_mul_index
      rw [hindex, hk0card, hKcard] at hmul
      have htrker_card : Nat.card tr.toAddMonoidHom.ker = q := by
        nlinarith
      have htrker_gt : 1 < Nat.card tr.toAddMonoidHom.ker := by
        rw [htrker_card]
        exact hq
      letI : Nontrivial tr.toAddMonoidHom.ker :=
        Finite.one_lt_card_iff_nontrivial.mp htrker_gt
      obtain ⟨ku, hku⟩ := exists_ne (0 : tr.toAddMonoidHom.ker)
      let k : K := ku
      have hk : k ≠ 0 := by
        intro hk0
        apply hku
        apply Subtype.ext
        exact hk0
      have htrk : tr k = 0 := by
        exact ku.property
      have hktrace : k + J.conj k = 0 := by
        rw [← htrace_formula, htrk, map_zero]
      let c0 : k0 := ⟨-1, by
        simp [k0, FixedBy.subfield]⟩
      obtain ⟨b, hb⟩ := hsurj c0
      have hbtrace : b + J.conj b + 1 = 0 := by
        have hb' : b + J.conj b = -(1 : K) := by
          rw [← htrace_formula, hb]
          rfl
        linear_combination hb'
      have hbktrace :
          (b + k) + J.conj (b + k) + 1 = 0 := by
        rw [map_add]
        linear_combination hbtrace + hktrace
      letI : FaithfulSMul G Omega := faithfulSMul_iff.mpr (by
        intro g hg
        rcases g.property with ⟨M, hM, hMg⟩
        let Mmat : Matrix (Fin 3) (Fin 3) K := M
        have hMfix (v : Fin 3 → K) (hv : v ≠ 0)
            (hiso : dotProduct (fun i => J.conj (v i))
              (J.form.mulVec v) = 0) :
            ∃ c : K, c • v = Mmat.mulVec v := by
          let z : Omega :=
            ⟨Projectivization.mk K v hv, ⟨v, hv, rfl, hiso⟩⟩
          have hz := congrArg Subtype.val (hg z)
          change (g : Matrix.ProjGenLinGroup (Fin 3) K) •
              Projectivization.mk K v hv = Projectivization.mk K v hv at hz
          rw [← hMg, Matrix.ProjGenLinGroup.mk_smul hscalar] at hz
          change Matrix.GeneralLinearGroup.toLin M •
              Projectivization.mk K v hv = Projectivization.mk K v hv at hz
          rw [Projectivization.smul_mk] at hz
          exact (Projectivization.mk_eq_mk_iff'
            K _ v _ hv).mp hz
        let e0 : Fin 3 → K := ![1, 0, 0]
        let e2 : Fin 3 → K := ![0, 0, 1]
        let w0 : Fin 3 → K := ![1, 0, k]
        let w1 : Fin 3 → K := ![1, 1, b]
        let w2 : Fin 3 → K := ![1, 1, b + k]
        have he0 : e0 ≠ 0 := by
          intro h
          have h0 := congrFun h (0 : Fin 3)
          simp [e0] at h0
        have he2 : e2 ≠ 0 := by
          intro h
          have h2 := congrFun h (2 : Fin 3)
          simp [e2] at h2
        have hw0 : w0 ≠ 0 := by
          intro h
          have h0 := congrFun h (0 : Fin 3)
          simp [w0] at h0
        have hw1 : w1 ≠ 0 := by
          intro h
          have h0 := congrFun h (0 : Fin 3)
          simp [w1] at h0
        have hw2 : w2 ≠ 0 := by
          intro h
          have h0 := congrFun h (0 : Fin 3)
          simp [w2] at h0
        have he0iso :
            dotProduct (fun i => J.conj (e0 i)) (J.form.mulVec e0) = 0 := by
          rw [hJstandard]
          simp [e0, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
        have he2iso :
            dotProduct (fun i => J.conj (e2 i)) (J.form.mulVec e2) = 0 := by
          rw [hJstandard]
          simp [e2, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
        have hw0iso :
            dotProduct (fun i => J.conj (w0 i)) (J.form.mulVec w0) = 0 := by
          rw [hJstandard]
          simpa [w0, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
            add_comm, add_left_comm, add_assoc] using hktrace
        have hw1iso :
            dotProduct (fun i => J.conj (w1 i)) (J.form.mulVec w1) = 0 := by
          rw [hJstandard]
          simpa [w1, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
            add_comm, add_left_comm, add_assoc, mul_comm] using hbtrace
        have hw2iso :
            dotProduct (fun i => J.conj (w2 i)) (J.form.mulVec w2) = 0 := by
          rw [hJstandard]
          simpa [w2, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
            add_comm, add_left_comm, add_assoc, mul_comm] using hbktrace
        obtain ⟨a0, ha0⟩ := hMfix e0 he0 he0iso
        obtain ⟨a2, ha2⟩ := hMfix e2 he2 he2iso
        obtain ⟨s0, hs0⟩ := hMfix w0 hw0 hw0iso
        obtain ⟨s1, hs1⟩ := hMfix w1 hw1 hw1iso
        obtain ⟨s2, hs2⟩ := hMfix w2 hw2 hw2iso
        have hM00 : Mmat 0 0 = a0 := by
          simpa [Mmat, e0, Matrix.mulVec, dotProduct,
            Fin.sum_univ_three] using (congrFun ha0 (0 : Fin 3)).symm
        have hM10 : Mmat 1 0 = 0 := by
          simpa [Mmat, e0, Matrix.mulVec, dotProduct,
            Fin.sum_univ_three] using (congrFun ha0 (1 : Fin 3)).symm
        have hM20 : Mmat 2 0 = 0 := by
          simpa [Mmat, e0, Matrix.mulVec, dotProduct,
            Fin.sum_univ_three] using (congrFun ha0 (2 : Fin 3)).symm
        have hM02 : Mmat 0 2 = 0 := by
          simpa [Mmat, e2, Matrix.mulVec, dotProduct,
            Fin.sum_univ_three] using (congrFun ha2 (0 : Fin 3)).symm
        have hM12 : Mmat 1 2 = 0 := by
          simpa [Mmat, e2, Matrix.mulVec, dotProduct,
            Fin.sum_univ_three] using (congrFun ha2 (1 : Fin 3)).symm
        have hM22 : Mmat 2 2 = a2 := by
          simpa [Mmat, e2, Matrix.mulVec, dotProduct,
            Fin.sum_univ_three] using (congrFun ha2 (2 : Fin 3)).symm
        have hs0a0 : s0 = a0 := by
          simpa [Mmat, w0, Matrix.mulVec, dotProduct,
            Fin.sum_univ_three, hM00, hM02] using congrFun hs0 (0 : Fin 3)
        have ha0a2 : a0 = a2 := by
          have hmul : a0 * k = a2 * k := by
            simpa [Mmat, w0, Matrix.mulVec, dotProduct,
              Fin.sum_univ_three, hs0a0, hM20, hM22] using
                congrFun hs0 (2 : Fin 3)
          exact mul_right_cancel₀ hk hmul
        have hs1mid : s1 = Mmat 1 1 := by
          simpa [Mmat, w1, Matrix.mulVec, dotProduct,
            Fin.sum_univ_three, hM10, hM12] using congrFun hs1 (1 : Fin 3)
        have hs2mid : s2 = Mmat 1 1 := by
          simpa [Mmat, w2, Matrix.mulVec, dotProduct,
            Fin.sum_univ_three, hM10, hM12] using congrFun hs2 (1 : Fin 3)
        have hs12 : s1 = s2 := hs1mid.trans hs2mid.symm
        have hs1a0 : s1 = a0 := by
          have hthird1 : s1 * b = Mmat 2 1 + a0 * b := by
            simpa [Mmat, w1, Matrix.mulVec, dotProduct,
              Fin.sum_univ_three, hM20, hM22, ha0a2.symm] using
                congrFun hs1 (2 : Fin 3)
          have hthird2 : s1 * (b + k) = Mmat 2 1 + a0 * (b + k) := by
            rw [hs12]
            simpa [Mmat, w2, Matrix.mulVec, dotProduct,
              Fin.sum_univ_three, hM20, hM22, ha0a2.symm] using
                congrFun hs2 (2 : Fin 3)
          have hmul : s1 * k = a0 * k := by
            linear_combination hthird2 - hthird1
          exact mul_right_cancel₀ hk hmul
        have hM01 : Mmat 0 1 = 0 := by
          have hfirst : s1 = a0 + Mmat 0 1 := by
            simpa [Mmat, w1, Matrix.mulVec, dotProduct,
              Fin.sum_univ_three, hM00, hM02] using congrFun hs1 (0 : Fin 3)
          rw [hs1a0] at hfirst
          apply add_left_cancel (a := a0)
          simpa using hfirst.symm
        have hM11 : Mmat 1 1 = a0 := hs1mid.symm.trans hs1a0
        have hM21 : Mmat 2 1 = 0 := by
          have hthird : s1 * b = Mmat 2 1 + a0 * b := by
            simpa [Mmat, w1, Matrix.mulVec, dotProduct,
              Fin.sum_univ_three, hM20, hM22, ha0a2.symm] using
                congrFun hs1 (2 : Fin 3)
          rw [hs1a0] at hthird
          apply add_right_cancel (b := a0 * b)
          simpa using hthird.symm
        have ha0ne : a0 ≠ 0 := by
          intro ha0zero
          have hMe0 : Mmat.mulVec e0 ≠ 0 := by
            intro hzero
            apply he0
            apply Matrix.mulVec_injective_of_isUnit (Units.isUnit M)
            simpa using hzero
          apply hMe0
          rw [← ha0]
          simp [ha0zero]
        have hMscalar : Mmat = Matrix.scalar (Fin 3) a0 := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.scalar_apply, hM00, hM01, hM02, hM10, hM11,
              hM12, hM20, hM21, hM22, ha0a2.symm]
        let au : Kˣ := Units.mk0 a0 ha0ne
        have hMeq : M = Matrix.GeneralLinearGroup.scalar (Fin 3) au := by
          apply Matrix.GeneralLinearGroup.ext
          intro i j
          change Mmat i j = Matrix.scalar (Fin 3) (au : K) i j
          rw [hMscalar]
          rfl
        apply Subtype.ext
        change (g : Matrix.ProjGenLinGroup (Fin 3) K) = 1
        rw [← hMg, hMeq, Matrix.ProjGenLinGroup.mk_scalar])
      exact (MulAction.toPerm_injective : Function.Injective
        (MulAction.toPerm : G → Equiv.Perm Omega))
    refine ⟨rho, h1012_curve_action_faithful, ?_⟩
    intro g z M hMg
    change (g : Matrix.ProjGenLinGroup (Fin 3) K) • (z : P) = _
    rw [← hMg, Matrix.ProjGenLinGroup.mk_smul hscalar]
    rfl
  rcases haction with ⟨rho, hrho, hrho_apply⟩
  let U : Subgroup G :=
    (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho
  let rootMatrix (z : S) : Matrix (Fin 3) (Fin 3) K :=
    hermitianUnipotentMatrix J z
  have hrootMatrixDet (z : S) : (rootMatrix z).det = 1 := by
    simp [rootMatrix, hermitianUnipotentMatrix, Matrix.det_fin_three]
  let rootGL (z : S) : GL (Fin 3) K :=
    hermitianUnipotentGL J z
  have hrootGLVal (z : S) :
      (rootGL z : Matrix (Fin 3) (Fin 3) K) = rootMatrix z := by
    rfl
  have hrootSpecial (z : S) : rootGL z ∈ J.specialSubgroup := by
    exact (hermitianUnipotentSU J hJstandard z).property
  let rootSU (z : S) : J.specialSubgroup :=
    ⟨rootGL z, hrootSpecial z⟩
  let rootG (z : S) : G :=
    ⟨Matrix.ProjGenLinGroup.mk (rootGL z),
      Subgroup.mem_map_of_mem Matrix.ProjGenLinGroup.mk (hrootSpecial z)⟩
  have hrootGVal (z : S) :
      (rootG z : Matrix.ProjGenLinGroup (Fin 3) K) =
        Matrix.ProjGenLinGroup.mk (rootGL z) := by
    rfl
  let rootZero : S := hermitianUnipotentOne J
  let rootMul (z w : S) : S := hermitianUnipotentMul J z w
  let rootInv (z : S) : S := hermitianUnipotentInv J z
  have hrootGLZero : rootGL rootZero = 1 := by
    change hermitianUnipotentGL J (hermitianUnipotentOne J) = 1
    exact congrArg Subtype.val (map_one (hermitianUnipotentSU J hJstandard))
  have hrootGLMul (z w : S) :
      rootGL z * rootGL w = rootGL (rootMul z w) := by
    change hermitianUnipotentGL J z * hermitianUnipotentGL J w =
      hermitianUnipotentGL J (hermitianUnipotentMul J z w)
    exact (congrArg Subtype.val
      (map_mul (hermitianUnipotentSU J hJstandard) z w)).symm
  have hrootGLInv (z : S) :
      (rootGL z)⁻¹ = rootGL (rootInv z) := by
    change (hermitianUnipotentGL J z)⁻¹ =
      hermitianUnipotentGL J (hermitianUnipotentInv J z)
    exact (congrArg Subtype.val
      (map_inv (hermitianUnipotentSU J hJstandard) z)).symm
  have hrootGZero : rootG rootZero = 1 := by
    apply Subtype.ext
    change Matrix.ProjGenLinGroup.mk (rootGL rootZero) = 1
    rw [hrootGLZero, map_one]
  have hrootGMul (z w : S) :
      rootG z * rootG w = rootG (rootMul z w) := by
    apply Subtype.ext
    change Matrix.ProjGenLinGroup.mk (rootGL z) *
        Matrix.ProjGenLinGroup.mk (rootGL w) =
      Matrix.ProjGenLinGroup.mk (rootGL (rootMul z w))
    rw [← map_mul, hrootGLMul]
  have hrootGInv (z : S) :
      (rootG z)⁻¹ = rootG (rootInv z) := by
    apply Subtype.ext
    change (Matrix.ProjGenLinGroup.mk (rootGL z))⁻¹ =
      Matrix.ProjGenLinGroup.mk (rootGL (rootInv z))
    rw [← map_inv, hrootGLInv]
  have hrootGInjective : Function.Injective rootG := by
    intro z w hzw
    let d := rootMul z (rootInv w)
    have hmk : Matrix.ProjGenLinGroup.mk (rootGL d) = 1 := by
      rw [← hrootGLMul, ← hrootGLInv, map_mul, map_inv]
      have hpgl := congrArg Subtype.val hzw
      change Matrix.ProjGenLinGroup.mk (rootGL z) =
        Matrix.ProjGenLinGroup.mk (rootGL w) at hpgl
      rw [hpgl, mul_inv_cancel]
    have hdcenter : rootGL d ∈ Subgroup.center (GL (Fin 3) K) := by
      rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
      exact hmk
    rcases Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
      hdcenter with ⟨c, hc⟩
    have hc_one : c = 1 := by
      have h00 := congrArg
        (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) hc
      rw [hrootGLVal] at h00
      simpa [rootMatrix, hermitianUnipotentMatrix,
        Matrix.scalar_apply] using h00
    have hd_one : rootGL d = 1 := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      have hij := congrArg
        (fun M : Matrix (Fin 3) (Fin 3) K => M i j) hc
      rw [hc_one] at hij
      simpa [Matrix.scalar_apply] using hij.symm
    have hgl : rootGL z = rootGL w := by
      rw [← hrootGLMul, ← hrootGLInv] at hd_one
      exact mul_inv_eq_one.mp hd_one
    apply Subtype.ext
    apply Prod.ext
    · have h01 := congrArg
        (fun M : GL (Fin 3) K =>
          (M : Matrix (Fin 3) (Fin 3) K) 0 1) hgl
      change (rootGL z : Matrix (Fin 3) (Fin 3) K) 0 1 =
        (rootGL w : Matrix (Fin 3) (Fin 3) K) 0 1 at h01
      rw [hrootGLVal, hrootGLVal] at h01
      simpa [rootMatrix, hermitianUnipotentMatrix] using h01
    · have h02 := congrArg
        (fun M : GL (Fin 3) K =>
          (M : Matrix (Fin 3) (Fin 3) K) 0 2) hgl
      change (rootGL z : Matrix (Fin 3) (Fin 3) K) 0 2 =
        (rootGL w : Matrix (Fin 3) (Fin 3) K) 0 2 at h02
      rw [hrootGLVal, hrootGLVal] at h02
      simpa [rootMatrix, hermitianUnipotentMatrix] using h02
  let R : Subgroup G :=
    { carrier := Set.range rootG
      one_mem' := ⟨rootZero, hrootGZero⟩
      mul_mem' := by
        rintro _ _ ⟨z, rfl⟩ ⟨w, rfl⟩
        exact ⟨rootMul z w, (hrootGMul z w).symm⟩
      inv_mem' := by
        rintro _ ⟨z, rfl⟩
        exact ⟨rootInv z, (hrootGInv z).symm⟩ }
  let toR (z : S) : R := ⟨rootG z, ⟨z, rfl⟩⟩
  have htoRBijective : Function.Bijective toR := by
    constructor
    · intro z w hzw
      apply hrootGInjective
      exact congrArg (fun r : R => (r : G)) hzw
    · intro r
      rcases r.property with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      exact hz
  let coordR : S ≃ R := Equiv.ofBijective toR htoRBijective
  have hcoordRMatrix (z : S) :
      ∃ M : GL (Fin 3) K,
        (M : Matrix (Fin 3) (Fin 3) K) =
            !![1, z.1.1, z.1.2;
               0, 1, -J.conj z.1.1;
               0, 0, 1] ∧
          ((((coordR z : R) : G) :
            Matrix.ProjGenLinGroup (Fin 3) K)) =
              Matrix.ProjGenLinGroup.mk M := by
    refine ⟨rootGL z, ?_, ?_⟩
    · rw [hrootGLVal]
      rfl
    · rfl
  have hRle : R ≤ U := by
    intro r hr
    rcases hr with ⟨z, rfl⟩
    change rho (rootG z) pinf = pinf
    apply Subtype.ext
    rw [hrho_apply (rootG z) pinf (rootSU z) (by rfl)]
    change (Matrix.GeneralLinearGroup.toLin (rootGL z)).toLinearEquiv •
        Projectivization.mk K vinf hvinf =
      Projectivization.mk K vinf hvinf
    rw [Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨1, ?_⟩
    change (1 : K) • vinf =
      (rootGL z : Matrix (Fin 3) (Fin 3) K).mulVec vinf
    rw [hrootGLVal]
    funext i
    fin_cases i <;>
      simp [rootMatrix, hermitianUnipotentMatrix, vinf,
        Matrix.mulVec]
  have hRcard : Nat.card R = q ^ 3 := by
    calc
      Nat.card R = Nat.card S := Nat.card_congr coordR.symm
      _ = q ^ 3 := hScard
  have haffineActMem (z w : S) :
      (w.1.2 + z.1.1 * w.1.1 + z.1.2) +
          J.conj (w.1.2 + z.1.1 * w.1.1 + z.1.2) +
          (w.1.1 - J.conj z.1.1) *
            J.conj (w.1.1 - J.conj z.1.1) = 0 := by
    rw [map_add, map_add, map_mul, map_sub, J.conj_involutive]
    linear_combination z.2 + w.2
  let affineAct (z w : S) : S :=
    ⟨(w.1.1 - J.conj z.1.1,
      w.1.2 + z.1.1 * w.1.1 + z.1.2), haffineActMem z w⟩
  have haffineActInjective (w : S) :
      Function.Injective (fun z : S => affineAct z w) := by
    intro z z' hzz'
    apply Subtype.ext
    apply Prod.ext
    · have hfirst := congrArg
        (fun x : S => x.1.1) hzz'
      change w.1.1 - J.conj z.1.1 =
        w.1.1 - J.conj z'.1.1 at hfirst
      exact J.conj.injective (sub_right_inj.mp hfirst)
    · have hfirst := congrArg
        (fun x : S => x.1.1) hzz'
      have hsecond := congrArg
        (fun x : S => x.1.2) hzz'
      change w.1.1 - J.conj z.1.1 =
        w.1.1 - J.conj z'.1.1 at hfirst
      have hza : z.1.1 = z'.1.1 := by
        exact J.conj.injective (sub_right_inj.mp hfirst)
      change w.1.2 + z.1.1 * w.1.1 + z.1.2 =
        w.1.2 + z'.1.1 * w.1.1 + z'.1.2 at hsecond
      rw [hza] at hsecond
      linear_combination hsecond
  have hrootActsAffine (z w : S) :
      rho (rootG z) (hOmegaEquiv.choose.symm (some w)) =
        hOmegaEquiv.choose.symm (some (affineAct z w)) := by
    apply Subtype.ext
    rw [hrho_apply (rootG z) (hOmegaEquiv.choose.symm (some w))
      (rootSU z) (by rfl)]
    rw [hOmegaEquiv.choose_spec.2 w,
      hOmegaEquiv.choose_spec.2 (affineAct z w)]
    rw [Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨1, ?_⟩
    change (1 : K) • vaff (affineAct z w) =
      (rootGL z : Matrix (Fin 3) (Fin 3) K).mulVec (vaff w)
    rw [hrootGLVal]
    funext i
    fin_cases i <;>
      simp [rootMatrix, hermitianUnipotentMatrix, vaff, affineAct,
        Matrix.mulVec]
    all_goals ring
  have hq : 1 < q := by
    let k0 := FixedBy.subfield K J.conj
    have hk0card : Nat.card k0 = q := by
      simpa [k0, FixedBy.subfield, RingAut.smul_def] using hfixed_card
    rw [← hk0card]
    exact Finite.one_lt_card
  have hnonfixed : ∃ u : K, J.conj u ≠ u := by
    by_contra h
    push Not at h
    let efixed : {r : K // J.conj r = r} ≃ K :=
      { toFun := fun r => r
        invFun := fun r => ⟨r, h r⟩
        left_inv := fun r => by ext; rfl
        right_inv := fun _ => rfl }
    have hcard : Nat.card {r : K // J.conj r = r} = Nat.card K :=
      Nat.card_congr efixed
    have hqq : q = q ^ 2 := hfixed_card.symm.trans (hcard.trans hKcard)
    nlinarith
  have hrootParamExists (a : K) : ∃ z : S, z.1.1 = a := by
    have hfixed :
        J.conj (-(a * J.conj a)) = -(a * J.conj a) := by
      rw [map_neg, map_mul, J.conj_involutive]
      ring
    obtain ⟨b, hb⟩ := huppert_II_10_4_trace_surjective
      J q hKcard hfixed_card (-(a * J.conj a)) hfixed
    refine ⟨⟨(a, b), ?_⟩, rfl⟩
    linear_combination hb
  have htraceZero_eq_sub_conj (b : K) (hb : b + J.conj b = 0) :
      ∃ c : K, c - J.conj c = b := by
    obtain ⟨u, hu⟩ := hnonfixed
    let delta := u - J.conj u
    have hdelta : delta ≠ 0 := by
      exact sub_ne_zero.mpr hu.symm
    have hconj_delta : J.conj delta = -delta := by
      dsimp [delta]
      rw [map_sub, J.conj_involutive]
      ring
    have hconj_b : J.conj b = -b := by
      linear_combination hb
    let k := b / delta
    have hkfixed : J.conj k = k := by
      dsimp [k]
      rw [map_div₀, hconj_b, hconj_delta]
      simp
    refine ⟨k * u, ?_⟩
    rw [map_mul, hkfixed]
    rw [← mul_sub, show u - J.conj u = delta from rfl]
    exact div_mul_cancel₀ b hdelta
  have htoRMul (z w : S) :
      toR z * toR w = toR (rootMul z w) := by
    apply Subtype.ext
    exact hrootGMul z w
  have hrootCommuteIff (z w : S) :
      toR z * toR w = toR w * toR z ↔
        z.1.1 * J.conj w.1.1 = w.1.1 * J.conj z.1.1 := by
    constructor
    · intro hcomm
      have hval := congrArg (fun r : R => (r : G)) hcomm
      change rootG z * rootG w = rootG w * rootG z at hval
      rw [hrootGMul, hrootGMul] at hval
      have hp := hrootGInjective hval
      have hsecond := congrArg (fun x : S => x.1.2) hp
      change z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1 =
        w.1.2 + z.1.2 - w.1.1 * J.conj z.1.1 at hsecond
      have hsecond' :
          (z.1.2 + w.1.2) - z.1.1 * J.conj w.1.1 =
            (z.1.2 + w.1.2) - w.1.1 * J.conj z.1.1 := by
        simpa [add_comm] using hsecond
      exact sub_right_inj.mp hsecond'
    · intro hcoord
      rw [htoRMul, htoRMul]
      apply congrArg toR
      apply Subtype.ext
      apply Prod.ext
      · change z.1.1 + w.1.1 = w.1.1 + z.1.1
        exact add_comm _ _
      · change z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1 =
          w.1.2 + z.1.2 - w.1.1 * J.conj z.1.1
        rw [hcoord]
        ring
  have htoRCenterIff (z : S) :
      toR z ∈ Subgroup.center R ↔ z.1.1 = 0 := by
    constructor
    · intro hzcenter
      have hzcomm (w : S) :
          toR z * toR w = toR w * toR z :=
        (Subgroup.mem_center_iff.mp hzcenter (toR w)).symm
      obtain ⟨w1, hw1⟩ := hrootParamExists 1
      have hfixed : z.1.1 = J.conj z.1.1 := by
        have hrel := (hrootCommuteIff z w1).mp (hzcomm w1)
        change z.1.1 * J.conj w1.1.1 =
          w1.1.1 * J.conj z.1.1 at hrel
        rw [hw1, map_one, mul_one, one_mul] at hrel
        exact hrel
      obtain ⟨u, hu⟩ := hnonfixed
      obtain ⟨wu, hwu⟩ := hrootParamExists u
      have hrel := (hrootCommuteIff z wu).mp (hzcomm wu)
      change z.1.1 * J.conj wu.1.1 =
        wu.1.1 * J.conj z.1.1 at hrel
      rw [hwu, ← hfixed] at hrel
      have hzero : z.1.1 * (J.conj u - u) = 0 := by
        calc
          z.1.1 * (J.conj u - u) =
              z.1.1 * J.conj u - z.1.1 * u := by ring
          _ = u * z.1.1 - z.1.1 * u := by rw [hrel]
          _ = 0 := by ring
      exact (mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr hu)
    · intro hza
      rw [Subgroup.mem_center_iff]
      intro y
      rcases y.property with ⟨w, hw⟩
      have hy : y = toR w := by
        apply Subtype.ext
        exact hw.symm
      rw [hy]
      exact (hrootCommuteIff z w).2 (by simp [hza]) |>.symm
  let toRHom : S →* R :=
    { toFun := toR
      map_one' := by
        apply Subtype.ext
        exact hrootGZero
      map_mul' := by
        intro z w
        exact (htoRMul z w).symm }
  have htoRCommutator (z w : S) :
      ⁅toR z, toR w⁆ = toR ⁅z, w⁆ := by
    exact (map_commutatorElement toRHom z w).symm
  have hRcomm : commutator R = Subgroup.center R := by
    apply le_antisymm
    · change ⁅(⊤ : Subgroup R), ⊤⁆ ≤ Subgroup.center R
      apply Subgroup.commutator_le.mpr
      intro x _ y _
      rcases x.property with ⟨z, hz⟩
      rcases y.property with ⟨w, hw⟩
      have hx : x = toR z := by
        apply Subtype.ext
        exact hz.symm
      have hy : y = toR w := by
        apply Subtype.ext
        exact hw.symm
      rw [hx, hy, htoRCommutator, hermitianUnipotent_commutator]
      exact (htoRCenterIff _).2 rfl
    · intro x hxcenter
      rcases x.property with ⟨z, hz⟩
      have hx : x = toR z := by
        apply Subtype.ext
        exact hz.symm
      have hza : z.1.1 = 0 :=
        (htoRCenterIff z).mp (hx ▸ hxcenter)
      have hzb : z.1.2 + J.conj z.1.2 = 0 := by
        have hzprop := z.property
        rw [hza] at hzprop
        simpa using hzprop
      obtain ⟨c, hc⟩ := htraceZero_eq_sub_conj z.1.2 hzb
      obtain ⟨p, hp⟩ := hrootParamExists 1
      obtain ⟨s, hs⟩ := hrootParamExists c
      have hcomm_mem : ⁅toR p, toR s⁆ ∈ commutator R :=
        Subgroup.commutator_mem_commutator
          (Subgroup.mem_top (toR p)) (Subgroup.mem_top (toR s))
      have hcomm_eq : ⁅toR p, toR s⁆ = toR z := by
        rw [htoRCommutator, hermitianUnipotent_commutator]
        apply congrArg toR
        apply Subtype.ext
        apply Prod.ext
        · exact hza.symm
        · change s.1.1 * J.conj p.1.1 -
            p.1.1 * J.conj s.1.1 = z.1.2
          rw [hp, hs, map_one, mul_one, one_mul]
          exact hc
      rw [hx, ← hcomm_eq]
      exact hcomm_mem
  have hRcommCard : Nat.card (commutator R) = q := by
    let T := {b : K // b + J.conj b = 0}
    let centralRoot (b : T) : S :=
      ⟨(0, b), by simpa using b.property⟩
    let centerParam (b : T) : Subgroup.center R :=
      ⟨toR (centralRoot b), (htoRCenterIff (centralRoot b)).mpr rfl⟩
    have hcenterParamBijective : Function.Bijective centerParam := by
      constructor
      · intro b c hbc
        have hval := congrArg
          (fun r : Subgroup.center R => (((r : R) : G))) hbc
        change rootG (centralRoot b) = rootG (centralRoot c) at hval
        have hcoord := hrootGInjective hval
        apply Subtype.ext
        exact congrArg (fun z : S => z.1.2) hcoord
      · intro r
        rcases (r : R).property with ⟨z, hz⟩
        have hrz : (r : R) = toR z := by
          apply Subtype.ext
          exact hz.symm
        have hzcenter : toR z ∈ Subgroup.center R := by
          rw [← hrz]
          exact r.property
        have hza : z.1.1 = 0 := (htoRCenterIff z).mp hzcenter
        have hzb : z.1.2 + J.conj z.1.2 = 0 := by
          have hzprop := z.property
          rw [hza] at hzprop
          simpa using hzprop
        refine ⟨⟨z.1.2, hzb⟩, ?_⟩
        apply Subtype.ext
        change toR (centralRoot ⟨z.1.2, hzb⟩) = (r : R)
        rw [hrz]
        apply congrArg toR
        apply Subtype.ext
        exact Prod.ext hza.symm rfl
    let centerEquiv : T ≃ Subgroup.center R :=
      Equiv.ofBijective centerParam hcenterParamBijective
    calc
      Nat.card (commutator R) = Nat.card (Subgroup.center R) := by
        rw [hRcomm]
      _ = Nat.card T := Nat.card_congr centerEquiv.symm
      _ = q := htraceZeroCard
  have hRregular :
      ∀ a b : Omega, a ≠ pinf → b ≠ pinf →
        ∃! r : R, rho (r : G) a = b := by
    let e := hOmegaEquiv.choose
    have heinf : e pinf = none := hOmegaEquiv.choose_spec.1
    letI : Fintype S := Fintype.ofFinite S
    intro a b ha hb
    have haSome : ∃ wa : S, e a = some wa := by
      cases hea : e a with
      | none =>
          exfalso
          apply ha
          apply e.injective
          rw [hea, heinf]
      | some wa => exact ⟨wa, rfl⟩
    have hbSome : ∃ wb : S, e b = some wb := by
      cases heb : e b with
      | none =>
          exfalso
          apply hb
          apply e.injective
          rw [heb, heinf]
      | some wb => exact ⟨wb, rfl⟩
    obtain ⟨wa, hwa⟩ := haSome
    obtain ⟨wb, hwb⟩ := hbSome
    have ha_repr : a = e.symm (some wa) := by
      apply e.injective
      rw [hwa, e.apply_symm_apply]
    have hb_repr : b = e.symm (some wb) := by
      apply e.injective
      rw [hwb, e.apply_symm_apply]
    have hsurj : Function.Surjective (fun z : S => affineAct z wa) :=
      Finite.injective_iff_surjective.mp (haffineActInjective wa)
    obtain ⟨z, hz⟩ := hsurj wb
    change affineAct z wa = wb at hz
    refine ⟨toR z, ?_, ?_⟩
    · change rho (rootG z) a = b
      rw [ha_repr, hb_repr]
      change rho (rootG z) (hOmegaEquiv.choose.symm (some wa)) =
        hOmegaEquiv.choose.symm (some wb)
      rw [hrootActsAffine, hz]
    · intro r hr
      rcases r.property with ⟨z', hz'⟩
      have hr' := hr
      change rho (r : G) a = b at hr'
      rw [← hz', ha_repr, hb_repr, hrootActsAffine] at hr'
      have haffine : affineAct z' wa = wb := by
        exact Option.some.inj (e.symm.injective hr')
      have hzz : z' = z :=
        haffineActInjective wa (haffine.trans hz.symm)
      apply Subtype.ext
      change (r : G) = rootG z
      rw [← hz', hzz]
  have hRstructure :
      ∃ R : Subgroup G,
        R ≤ U ∧
        Nat.card R = q ^ 3 ∧
        commutator R = Subgroup.center R ∧
        Nat.card (commutator R) = q ∧
        (∀ a b : Omega, a ≠ pinf → b ≠ pinf →
          ∃! r : R, rho (r : G) a = b) ∧
        ∃ coordR :
            {z : K × K //
              z.2 + J.conj z.2 + z.1 * J.conj z.1 = 0} ≃ R,
          ∀ z : {z : K × K //
              z.2 + J.conj z.2 + z.1 * J.conj z.1 = 0},
            ∃ M : GL (Fin 3) K,
              (M : Matrix (Fin 3) (Fin 3) K) =
                !![1, (z : K × K).1, (z : K × K).2;
                   0, 1, -J.conj (z : K × K).1;
                   0, 0, 1] ∧
              ((((coordR z : R) : G) :
                Matrix.ProjGenLinGroup (Fin 3) K)) =
                  Matrix.ProjGenLinGroup.mk M := by
    exact ⟨R, hRle, hRcard, hRcomm, hRcommCard, hRregular,
      coordR, hcoordRMatrix⟩
  rcases hRstructure with
    ⟨R, hRle, hRcard, hRcomm, hRcomm_card,
      hRregular, hRcoordinates⟩
  let torusMatrix (k : Kˣ) : Matrix (Fin 3) (Fin 3) K :=
    hermitianTorusMatrix J k
  have htorusMatrixDet (k : Kˣ) : (torusMatrix k).det = 1 := by
    change (hermitianTorusMatrix J k).det = 1
    have hk : (k : K) ≠ 0 := Units.ne_zero k
    have hconjk : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk
    simp [hermitianTorusMatrix, Matrix.det_fin_three, hk, hconjk]
  let torusGL (k : Kˣ) : GL (Fin 3) K :=
    hermitianTorusGL J k
  have htorusGLVal (k : Kˣ) :
      (torusGL k : Matrix (Fin 3) (Fin 3) K) = torusMatrix k := by
    rfl
  have htorusSpecial (k : Kˣ) : torusGL k ∈ J.specialSubgroup := by
    exact (hermitianTorusSU J hJstandard k).property
  let torusG (k : Kˣ) : G :=
    ⟨Matrix.ProjGenLinGroup.mk (torusGL k),
      Subgroup.mem_map_of_mem Matrix.ProjGenLinGroup.mk (htorusSpecial k)⟩
  have htorusGOne : torusG 1 = 1 := by
    apply Subtype.ext
    change Matrix.ProjGenLinGroup.mk (torusGL 1) = 1
    have hgl := congrArg Subtype.val
      (map_one (hermitianTorusSU J hJstandard))
    change torusGL 1 = 1 at hgl
    rw [hgl, map_one]
  have htorusGMul (k l : Kˣ) :
      torusG (k * l) = torusG k * torusG l := by
    apply Subtype.ext
    change Matrix.ProjGenLinGroup.mk (torusGL (k * l)) =
      Matrix.ProjGenLinGroup.mk (torusGL k) *
        Matrix.ProjGenLinGroup.mk (torusGL l)
    have hgl := congrArg Subtype.val
      (map_mul (hermitianTorusSU J hJstandard) k l)
    change torusGL (k * l) = torusGL k * torusGL l at hgl
    rw [hgl, map_mul]
  let torusHom : Kˣ →* G :=
    { toFun := torusG
      map_one' := htorusGOne
      map_mul' := htorusGMul }
  let H : Subgroup G := torusHom.range
  have hHle : H ≤ U := by
    intro h hh
    rcases hh with ⟨k, rfl⟩
    change rho (torusG k) pinf = pinf
    apply Subtype.ext
    rw [hrho_apply (torusG k) pinf (hermitianTorusSU J hJstandard k)
      (by rfl)]
    change (Matrix.GeneralLinearGroup.toLin (torusGL k)).toLinearEquiv •
        Projectivization.mk K vinf hvinf =
      Projectivization.mk K vinf hvinf
    rw [Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨(J.conj (k : K))⁻¹, ?_⟩
    change (J.conj (k : K))⁻¹ • vinf =
      (torusGL k : Matrix (Fin 3) (Fin 3) K).mulVec vinf
    rw [htorusGLVal]
    funext i
    fin_cases i <;>
      simp [torusMatrix, hermitianTorusMatrix, vinf,
        Matrix.mulVec]
  have hHcyclic : IsCyclic H := by
    letI : IsCyclic Kˣ := inferInstance
    exact isCyclic_of_surjective torusHom.rangeRestrict
      torusHom.rangeRestrict_surjective
  have htorusMemKerIff (k : Kˣ) :
      k ∈ torusHom.ker ↔
        (k : K) ^ (q + 1) = 1 ∧ (k : K) ^ 3 = 1 := by
    constructor
    · intro hkern
      have hpgl : Matrix.ProjGenLinGroup.mk (torusGL k) = 1 := by
        have h := congrArg Subtype.val
          (show torusHom k = 1 from (MonoidHom.mem_ker.mp hkern))
        exact h
      have hcenter : torusGL k ∈ Subgroup.center (GL (Fin 3) K) := by
        rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
        exact hpgl
      rcases Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
        hcenter with ⟨c, hc⟩
      have h0 := congrArg
        (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) hc
      have h1 := congrArg
        (fun M : Matrix (Fin 3) (Fin 3) K => M 1 1) hc
      have h2 := congrArg
        (fun M : Matrix (Fin 3) (Fin 3) K => M 2 2) hc
      rw [htorusGLVal] at h0 h1 h2
      have h02 : (J.conj (k : K))⁻¹ = (k : K) := by
        exact (by
          simpa [torusMatrix, hermitianTorusMatrix, Matrix.scalar_apply]
            using h0.symm.trans h2)
      have h12 : J.conj (k : K) * (k : K)⁻¹ = (k : K) := by
        exact (by
          simpa [torusMatrix, hermitianTorusMatrix, Matrix.scalar_apply]
            using h1.symm.trans h2)
      have hk : (k : K) ≠ 0 := Units.ne_zero k
      have hconjk : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk
      have hnorm : J.conj (k : K) * (k : K) = 1 := by
        calc
          J.conj (k : K) * (k : K) =
              J.conj (k : K) * (J.conj (k : K))⁻¹ := by rw [h02]
          _ = 1 := mul_inv_cancel₀ hconjk
      have hsq : J.conj (k : K) = (k : K) * (k : K) := by
        calc
          J.conj (k : K) =
              J.conj (k : K) * ((k : K)⁻¹ * (k : K)) := by
                rw [inv_mul_cancel₀ hk, mul_one]
          _ = (J.conj (k : K) * (k : K)⁻¹) * (k : K) := by ring
          _ = (k : K) * (k : K) := by rw [h12]
      constructor
      · rw [pow_succ, ← huppert_II_10_4_conj_eq_frobenius
          J q hKcard hfixed_card]
        exact hnorm
      · calc
          (k : K) ^ 3 = ((k : K) * (k : K)) * (k : K) := by ring
          _ = J.conj (k : K) * (k : K) := by rw [← hsq]
          _ = 1 := hnorm
    · rintro ⟨hnormPow, hcube⟩
      have hk : (k : K) ≠ 0 := Units.ne_zero k
      have hconjk : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk
      have hconjFormula : J.conj (k : K) = (k : K) ^ q :=
        huppert_II_10_4_conj_eq_frobenius
          J q hKcard hfixed_card (k : K)
      have hnorm : J.conj (k : K) * (k : K) = 1 := by
        rw [hconjFormula]
        simpa [pow_succ] using hnormPow
      have h0 : (J.conj (k : K))⁻¹ = (k : K) := by
        calc
          (J.conj (k : K))⁻¹ =
              (J.conj (k : K))⁻¹ *
                (J.conj (k : K) * (k : K)) := by rw [hnorm, mul_one]
          _ = ((J.conj (k : K))⁻¹ * J.conj (k : K)) * (k : K) := by ring
          _ = (k : K) := by rw [inv_mul_cancel₀ hconjk, one_mul]
      have hconjInv : J.conj (k : K) = (k : K)⁻¹ := by
        calc
          J.conj (k : K) =
              J.conj (k : K) * ((k : K) * (k : K)⁻¹) := by
                rw [mul_inv_cancel₀ hk, mul_one]
          _ = (J.conj (k : K) * (k : K)) * (k : K)⁻¹ := by ring
          _ = (k : K)⁻¹ := by rw [hnorm, one_mul]
      have h1 : J.conj (k : K) * (k : K)⁻¹ = (k : K) := by
        rw [hconjInv]
        field_simp [hk]
        simpa [pow_succ, pow_two] using hcube.symm
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      change Matrix.ProjGenLinGroup.mk (torusGL k) = 1
      rw [← MonoidHom.mem_ker, Matrix.ProjGenLinGroup.ker_mk]
      apply Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
      refine ⟨(k : K), ?_⟩
      rw [htorusGLVal]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [torusMatrix, hermitianTorusMatrix, Matrix.scalar_apply, h0, h1]
  have htorusKerCard :
      Nat.card torusHom.ker = Nat.gcd (q + 1) 3 := by
    have htorus_mem_ker_iff (k : Kˣ) :
        k ∈ torusHom.ker ↔
          (k : K) ^ (q + 1) = 1 ∧ (k : K) ^ 3 = 1 := by
      rw [MonoidHom.mem_ker]
      constructor
      · intro hkern
        have hpgl : Matrix.ProjGenLinGroup.mk (torusGL k) = 1 :=
          congrArg Subtype.val hkern
        have hcenter : torusGL k ∈ Subgroup.center (GL (Fin 3) K) := by
          rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
          exact hpgl
        rcases
            Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
              hcenter with ⟨c, hc⟩
        have h00 := congrArg
          (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) hc
        have h11 := congrArg
          (fun M : Matrix (Fin 3) (Fin 3) K => M 1 1) hc
        have h22 := congrArg
          (fun M : Matrix (Fin 3) (Fin 3) K => M 2 2) hc
        rw [htorusGLVal] at h00 h11 h22
        simp [torusMatrix, hermitianTorusMatrix,
          Matrix.scalar_apply] at h00 h11 h22
        have hd0 : (J.conj (k : K))⁻¹ = (k : K) :=
          h00.symm.trans h22
        have hmid : J.conj (k : K) * (k : K)⁻¹ = (k : K) :=
          h11.symm.trans h22
        have hk0 : (k : K) ≠ 0 := Units.ne_zero k
        have hconjk0 : J.conj (k : K) ≠ 0 :=
          (map_ne_zero J.conj).mpr hk0
        have hnorm : J.conj (k : K) * (k : K) = 1 := by
          have h := congrArg
            (fun x : K => J.conj (k : K) * x) hd0
          simpa [hconjk0] using h.symm
        have hsq : J.conj (k : K) = (k : K) * (k : K) := by
          have h := congrArg (fun x : K => x * (k : K)) hmid
          simpa [mul_assoc, hk0] using h
        have hconjpow : J.conj (k : K) = (k : K) ^ q :=
          huppert_II_10_4_conj_eq_frobenius
            J q hKcard hfixed_card (k : K)
        constructor
        · rw [pow_succ, ← hconjpow, hnorm]
        · calc
            (k : K) ^ 3 = ((k : K) * (k : K)) * (k : K) := by ring
            _ = J.conj (k : K) * (k : K) := by rw [← hsq]
            _ = 1 := hnorm
      · rintro ⟨hqpow, hthree⟩
        have hk0 : (k : K) ≠ 0 := Units.ne_zero k
        have hconjpow : J.conj (k : K) = (k : K) ^ q :=
          huppert_II_10_4_conj_eq_frobenius
            J q hKcard hfixed_card (k : K)
        have hnorm : J.conj (k : K) * (k : K) = 1 := by
          rw [hconjpow]
          simpa [pow_succ] using hqpow
        have hd0 : (J.conj (k : K))⁻¹ = (k : K) := by
          calc
            (J.conj (k : K))⁻¹ =
                (J.conj (k : K))⁻¹ *
                  (J.conj (k : K) * (k : K)) := by rw [hnorm, mul_one]
            _ = ((J.conj (k : K))⁻¹ * J.conj (k : K)) * (k : K) := by ring
            _ = (k : K) := by
              rw [inv_mul_cancel₀ ((map_ne_zero J.conj).2 hk0), one_mul]
        have hconjEq : J.conj (k : K) = (k : K)⁻¹ :=
          eq_inv_of_mul_eq_one_left hnorm
        have hkInv : (k : K)⁻¹ = (k : K) * (k : K) := by
          apply mul_left_cancel₀ hk0
          calc
            (k : K) * (k : K)⁻¹ = 1 := mul_inv_cancel₀ hk0
            _ = (k : K) ^ 3 := hthree.symm
            _ = (k : K) * ((k : K) * (k : K)) := by ring
        have hmid : J.conj (k : K) * (k : K)⁻¹ = (k : K) := by
          rw [hconjEq, hkInv]
          calc
            ((k : K) * (k : K)) * ((k : K) * (k : K)) =
                (k : K) * ((k : K) ^ 3) := by ring
            _ = (k : K) * 1 := congrArg (fun x : K => (k : K) * x) hthree
            _ = (k : K) := mul_one _
        apply Subtype.ext
        change Matrix.ProjGenLinGroup.mk (torusGL k) = 1
        rw [← MonoidHom.mem_ker, Matrix.ProjGenLinGroup.ker_mk,
          Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
        refine ⟨(k : K), ?_⟩
        rw [htorusGLVal]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [torusMatrix, hermitianTorusMatrix,
            Matrix.scalar_apply, hd0, hmid]
    have hkerEq :
        torusHom.ker = rootsOfUnity (q + 1) K ⊓ rootsOfUnity 3 K := by
      ext k
      rw [htorus_mem_ker_iff, Subgroup.mem_inf,
        mem_rootsOfUnity, mem_rootsOfUnity]
      constructor
      · rintro ⟨hqpow, hthree⟩
        constructor
        · apply Units.ext
          simpa using hqpow
        · apply Units.ext
          simpa using hthree
      · rintro ⟨hqpow, hthree⟩
        constructor
        · simpa using congrArg Units.val hqpow
        · simpa using congrArg Units.val hthree
    letI : IsCyclic Kˣ := inferInstance
    have hcardUnits : Nat.card Kˣ = q ^ 2 - 1 := by
      rw [Nat.card_units, hKcard]
    have hd : Nat.gcd (q + 1) 3 ∣ q ^ 2 - 1 := by
      have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
        simpa [mul_comm] using Nat.sq_sub_sq q 1
      rw [hfactor]
      exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (q + 1) 3) _
    rw [hkerEq, rootsOfUnity_inf_rootsOfUnity,
      rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker,
      hcardUnits, Nat.gcd_eq_right hd]
  have hHcard :
      Nat.card H = (q ^ 2 - 1) / Nat.gcd (q + 1) 3 := by
    have hmul := torusHom.ker.card_mul_index
    rw [Subgroup.index_ker] at hmul
    change Nat.card torusHom.ker * Nat.card H = Nat.card Kˣ at hmul
    rw [htorusKerCard, Nat.card_units, hKcard] at hmul
    calc
      Nat.card H =
          (Nat.gcd (q + 1) 3 * Nat.card H) / Nat.gcd (q + 1) 3 := by
        symm
        have hdpos : 0 < Nat.gcd (q + 1) 3 :=
          Nat.gcd_pos_of_pos_left 3 (Nat.succ_pos q)
        exact Nat.mul_div_right (Nat.card H) hdpos
      _ = (q ^ 2 - 1) / Nat.gcd (q + 1) 3 := by rw [hmul]
  have hHcoordinates :
      ∀ h : H,
        ∃ k : Kˣ, ∃ M : GL (Fin 3) K,
          (M : Matrix (Fin 3) (Fin 3) K) =
            !![(J.conj (k : K))⁻¹, 0, 0;
               0, J.conj (k : K) * (k : K)⁻¹, 0;
               0, 0, (k : K)] ∧
          ((((h : H) : G) : Matrix.ProjGenLinGroup (Fin 3) K)) =
            Matrix.ProjGenLinGroup.mk M := by
    intro h
    rcases h.property with ⟨k, hk⟩
    refine ⟨k, torusGL k, ?_, ?_⟩
    · rw [htorusGLVal]
      rfl
    · exact (congrArg
        (fun g : G => (g : Matrix.ProjGenLinGroup (Fin 3) K)) hk).symm
  have hHcoordinates_surjective :
      ∀ k : Kˣ,
        ∃ h : H, ∃ M : GL (Fin 3) K,
          (M : Matrix (Fin 3) (Fin 3) K) =
            !![(J.conj (k : K))⁻¹, 0, 0;
               0, J.conj (k : K) * (k : K)⁻¹, 0;
               0, 0, (k : K)] ∧
          ((((h : H) : G) : Matrix.ProjGenLinGroup (Fin 3) K)) =
            Matrix.ProjGenLinGroup.mk M := by
    intro k
    let h : H := ⟨torusG k, ⟨k, rfl⟩⟩
    refine ⟨h, torusGL k, ?_, ?_⟩
    · rw [htorusGLVal]
      rfl
    · rfl
  have hHstructure :
      ∃ H : Subgroup G,
        H ≤ U ∧ IsCyclic H ∧
        Nat.card H = (q ^ 2 - 1) / Nat.gcd (q + 1) 3 ∧
        (∀ h : H,
          ∃ k : Kˣ, ∃ M : GL (Fin 3) K,
            (M : Matrix (Fin 3) (Fin 3) K) =
              !![(J.conj (k : K))⁻¹, 0, 0;
                 0, J.conj (k : K) * (k : K)⁻¹, 0;
                 0, 0, (k : K)] ∧
            ((((h : H) : G) : Matrix.ProjGenLinGroup (Fin 3) K)) =
              Matrix.ProjGenLinGroup.mk M) ∧
        ∀ k : Kˣ,
          ∃ h : H, ∃ M : GL (Fin 3) K,
            (M : Matrix (Fin 3) (Fin 3) K) =
              !![(J.conj (k : K))⁻¹, 0, 0;
                 0, J.conj (k : K) * (k : K)⁻¹, 0;
                 0, 0, (k : K)] ∧
            ((((h : H) : G) : Matrix.ProjGenLinGroup (Fin 3) K)) =
              Matrix.ProjGenLinGroup.mk M := by
    exact ⟨H, hHle, hHcyclic, hHcard, hHcoordinates,
      hHcoordinates_surjective⟩
  rcases hHstructure with
    ⟨H, hHle, hHcyclic, hHcard, hHcoordinates,
      hHcoordinates_surjective⟩
  let pzero : Omega := hOmegaEquiv.choose.symm (some rootZero)
  have hpzero_ne : pzero ≠ pinf := by
    intro h
    have heq := congrArg hOmegaEquiv.choose h
    rw [hOmegaEquiv.choose.apply_symm_apply,
      hOmegaEquiv.choose_spec.1] at heq
    contradiction
  have hHfixZero : ∀ h : H, rho (h : G) pzero = pzero := by
    intro h
    rcases hHcoordinates h with ⟨k, M, hM, hproj⟩
    have hMtorus : M = torusGL k := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change (M : Matrix (Fin 3) (Fin 3) K) i j =
        (torusGL k : Matrix (Fin 3) (Fin 3) K) i j
      rw [hM, htorusGLVal]
      rfl
    have hh : (h : G) = torusG k := by
      apply Subtype.ext
      exact hproj.trans (by rw [hMtorus])
    rw [hh]
    apply Subtype.ext
    rw [hrho_apply (torusG k) pzero (hermitianTorusSU J hJstandard k)
      (by rfl)]
    rw [hOmegaEquiv.choose_spec.2 rootZero]
    rw [Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨(k : K), ?_⟩
    change (k : K) • vaff rootZero =
      (torusGL k : Matrix (Fin 3) (Fin 3) K).mulVec (vaff rootZero)
    rw [htorusGLVal]
    funext i
    fin_cases i <;>
      simp [torusMatrix, hermitianTorusMatrix, vaff, rootZero,
        hermitianUnipotentOne, Matrix.mulVec]
  have hdoubleFix_mem_H (g : G)
      (hginf : rho g pinf = pinf)
      (hgzero : rho g pzero = pzero) : g ∈ H := by
    rcases g.property with ⟨M, hM, hMg⟩
    let Mu : J.specialSubgroup := ⟨M, hM⟩
    let Mmat : Matrix (Fin 3) (Fin 3) K := M
    have hinf := congrArg Subtype.val hginf
    rw [hrho_apply g pinf Mu hMg] at hinf
    change (Matrix.GeneralLinearGroup.toLin M).toLinearEquiv •
        Projectivization.mk K vinf hvinf =
      Projectivization.mk K vinf hvinf at hinf
    rw [Projectivization.smul_mk] at hinf
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff'
      K _ _ _ _).mp hinf
    have hzero := congrArg Subtype.val hgzero
    rw [hrho_apply g pzero Mu hMg] at hzero
    rw [hOmegaEquiv.choose_spec.2 rootZero] at hzero
    rw [Projectivization.smul_mk] at hzero
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff'
      K _ _ _ _).mp hzero
    have h00 : Mmat 0 0 = a := by
      simpa [Mmat, vinf, Matrix.mulVec, Fin.sum_univ_three,
        Matrix.vecHead] using
        (congrFun ha (0 : Fin 3)).symm
    have h10 : Mmat 1 0 = 0 := by
      simpa [Mmat, vinf, Matrix.mulVec, Fin.sum_univ_three,
        Matrix.vecHead] using
        (congrFun ha (1 : Fin 3)).symm
    have h20 : Mmat 2 0 = 0 := by
      simpa [Mmat, vinf, Matrix.mulVec, Fin.sum_univ_three,
        Matrix.vecHead] using
        (congrFun ha (2 : Fin 3)).symm
    have h02 : Mmat 0 2 = 0 := by
      simpa [Mmat, vaff, rootZero, hermitianUnipotentOne,
        Matrix.mulVec, Fin.sum_univ_three, Matrix.vecHead,
        Matrix.vecTail] using
          (congrFun hc (0 : Fin 3)).symm
    have h12 : Mmat 1 2 = 0 := by
      simpa [Mmat, vaff, rootZero, hermitianUnipotentOne,
        Matrix.mulVec, Fin.sum_univ_three, Matrix.vecHead,
        Matrix.vecTail] using
          (congrFun hc (1 : Fin 3)).symm
    have h22 : Mmat 2 2 = c := by
      simpa [Mmat, vaff, rootZero, hermitianUnipotentOne,
        Matrix.mulVec, Fin.sum_univ_three, Matrix.vecHead,
        Matrix.vecTail] using
          (congrFun hc (2 : Fin 3)).symm
    have ha0 : a ≠ 0 := by
      intro hazero
      have hMv : Mmat.mulVec vinf ≠ 0 := by
        intro hz
        apply hvinf
        exact (Matrix.mulVec_injective_of_isUnit (Units.isUnit M))
          (by simpa [Mmat] using hz)
      apply hMv
      funext i
      fin_cases i <;>
        simp [vinf, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
          h00, h10, h20, hazero]
    have hc0 : c ≠ 0 := by
      intro hczero
      have hvzero : vaff rootZero ≠ 0 := hvaff rootZero
      have hMv : Mmat.mulVec (vaff rootZero) ≠ 0 := by
        intro hz
        apply hvzero
        exact (Matrix.mulVec_injective_of_isUnit (Units.isUnit M))
          (by simpa [Mmat] using hz)
      apply hMv
      funext i
      fin_cases i <;>
        simp [vaff, rootZero, hermitianUnipotentOne,
          Matrix.mulVec, dotProduct, Fin.sum_univ_three,
          h02, h12, h22, hczero]
    have hunit := (J.mem_specialSubgroup_iff M).mp hM |>.1
    rw [hJstandard] at hunit
    have hu01 := congrArg
      (fun X : Matrix (Fin 3) (Fin 3) K => X 0 1) hunit
    have hu21 := congrArg
      (fun X : Matrix (Fin 3) (Fin 3) K => X 2 1) hunit
    have hu02 := congrArg
      (fun X : Matrix (Fin 3) (Fin 3) K => X 0 2) hunit
    have h21 : Mmat 2 1 = 0 := by
      have hprod : J.conj a * Mmat 2 1 = 0 := by
        simpa [Mmat, HermitianForm.conjTranspose, Matrix.mul_apply,
          Fin.sum_univ_three, h00, h10, h20, h02, h12,
          map_zero] using hu01
      exact (mul_eq_zero.mp hprod).resolve_left ((map_ne_zero J.conj).2 ha0)
    have h01 : Mmat 0 1 = 0 := by
      have hprod : J.conj c * Mmat 0 1 = 0 := by
        simpa [Mmat, HermitianForm.conjTranspose, Matrix.mul_apply,
          Fin.sum_univ_three, h00, h10, h20, h02, h12, h22,
          map_zero] using hu21
      exact (mul_eq_zero.mp hprod).resolve_left ((map_ne_zero J.conj).2 hc0)
    have hac : J.conj a * c = 1 := by
      simpa [Mmat, HermitianForm.conjTranspose, Matrix.mul_apply,
        Fin.sum_univ_three, h00, h10, h20, h02, h12, h22,
        map_zero] using hu02
    have hac' : a * J.conj c = 1 := by
      have h := congrArg J.conj hac
      rw [map_mul, map_one, J.conj_involutive] at h
      exact h
    have haDiag : a = (J.conj c)⁻¹ :=
      eq_inv_of_mul_eq_one_left hac'
    have hdet := congrArg Units.val
      ((J.mem_specialSubgroup_iff M).mp hM |>.2)
    have hdet' : a * Mmat 1 1 * c = 1 := by
      have hdet0 : a * Mmat 1 1 * Mmat 2 2 = 1 := by
        simpa [Mmat, Matrix.det_fin_three, h00, h10, h20, h02, h12,
          h01, h21] using hdet
      rw [h22] at hdet0
      exact hdet0
    have hconjc0 : J.conj c ≠ 0 := (map_ne_zero J.conj).2 hc0
    have hmc : Mmat 1 1 * c = J.conj c := by
      have h := congrArg (fun x : K => J.conj c * x) hdet'
      rw [haDiag] at h
      simpa [hconjc0, mul_assoc] using h
    have hmDiag : Mmat 1 1 = J.conj c * c⁻¹ := by
      calc
        Mmat 1 1 = Mmat 1 1 * (c * c⁻¹) := by rw [mul_inv_cancel₀ hc0, mul_one]
        _ = (Mmat 1 1 * c) * c⁻¹ := by ring
        _ = J.conj c * c⁻¹ := by rw [hmc]
    let k : Kˣ := Units.mk0 c hc0
    have hMtorus : M = torusGL k := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change Mmat i j =
        (torusGL k : Matrix (Fin 3) (Fin 3) K) i j
      rw [htorusGLVal]
      fin_cases i <;> fin_cases j <;>
        simp [torusMatrix, hermitianTorusMatrix, k, h00, h10, h20,
          h01, h21, h02, h12, h22, haDiag, hmDiag]
    obtain ⟨h, N, hN, hNproj⟩ := hHcoordinates_surjective k
    have hNtorus : N = torusGL k := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change (N : Matrix (Fin 3) (Fin 3) K) i j =
        (torusGL k : Matrix (Fin 3) (Fin 3) K) i j
      rw [hN, htorusGLVal]
      rfl
    have hgh : g = (h : G) := by
      apply Subtype.ext
      calc
        (g : Matrix.ProjGenLinGroup (Fin 3) K) =
            Matrix.ProjGenLinGroup.mk M := hMg.symm
        _ = Matrix.ProjGenLinGroup.mk N := by rw [hMtorus, hNtorus]
        _ = ((h : H) : Matrix.ProjGenLinGroup (Fin 3) K) := hNproj.symm
    rw [hgh]
    exact h.property
  have hHnormal : H ≤ Subgroup.normalizer R := by
    rcases hRcoordinates with ⟨coordR, hcoordRMatrix⟩
    intro h hh
    letI : Finite R := Finite.of_injective
      coordR.symm coordR.symm.injective
    refine Subgroup.mem_normalizer_fintype ?_
    intro r hr
    let rR : R := ⟨r, hr⟩
    let z : S := coordR.symm rR
    have hcoordRz : ((coordR z : R) : G) = r := by
      change ((coordR (coordR.symm rR) : R) : G) = r
      rw [coordR.apply_symm_apply]
    rcases hcoordRMatrix z with ⟨N, hN, hNproj⟩
    rcases hHcoordinates ⟨h, hh⟩ with ⟨k, M, hM, hMproj⟩
    let z' := hermitianTorusAction J k z
    have hcomm := hermitianTorusGL_mul_unipotent J k z
    rcases hcoordRMatrix z' with ⟨N', hN', hN'proj⟩
    have hMtorus : M = torusGL k := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change (M : Matrix (Fin 3) (Fin 3) K) i j =
        (torusGL k : Matrix (Fin 3) (Fin 3) K) i j
      rw [hM, htorusGLVal]
      rfl
    have hNroot : N = rootGL z := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change (N : Matrix (Fin 3) (Fin 3) K) i j =
        (rootGL z : Matrix (Fin 3) (Fin 3) K) i j
      rw [hN, hrootGLVal]
      rfl
    have hN'root : N' = rootGL z' := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change (N' : Matrix (Fin 3) (Fin 3) K) i j =
        (rootGL z' : Matrix (Fin 3) (Fin 3) K) i j
      rw [hN', hrootGLVal]
      rfl
    have hGLconj : M * N * M⁻¹ = N' := by
      rw [hMtorus, hNroot, hN'root]
      change
        hermitianTorusGL J k * hermitianUnipotentGL J z *
            (hermitianTorusGL J k)⁻¹ =
          hermitianUnipotentGL J z'
      calc
        hermitianTorusGL J k * hermitianUnipotentGL J z *
              (hermitianTorusGL J k)⁻¹ =
            (hermitianUnipotentGL J z' * hermitianTorusGL J k) *
              (hermitianTorusGL J k)⁻¹ := by rw [hcomm]
        _ = hermitianUnipotentGL J z' := by group
    have hrproj :
        (r : Matrix.ProjGenLinGroup (Fin 3) K) =
          Matrix.ProjGenLinGroup.mk N := by
      rw [← hcoordRz]
      exact hNproj
    have hconjEq : h * r * h⁻¹ = ((coordR z' : R) : G) := by
      apply Subtype.ext
      change
        (h : Matrix.ProjGenLinGroup (Fin 3) K) *
              (r : Matrix.ProjGenLinGroup (Fin 3) K) *
              (h : Matrix.ProjGenLinGroup (Fin 3) K)⁻¹ =
            (((coordR z' : R) : G) :
              Matrix.ProjGenLinGroup (Fin 3) K)
      rw [hMproj, hrproj, hN'proj, ← map_inv, ← map_mul, ← map_mul,
        hGLconj]
    rw [hconjEq]
    exact (coordR z').property
  have hRinfH : R ⊓ H = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    let xr : R := ⟨x, hx.1⟩
    have hxfix : rho (xr : G) pzero = pzero :=
      hHfixZero ⟨x, hx.2⟩
    have h1fix : rho ((1 : R) : G) pzero = pzero := by simp
    rcases hRregular pzero pzero hpzero_ne hpzero_ne with
      ⟨r, hr, hunique⟩
    have hxr : xr = r := hunique xr hxfix
    have h1r : (1 : R) = r := hunique 1 h1fix
    exact congrArg Subtype.val (hxr.trans h1r.symm)
  have hRsupH : R ⊔ H = U := by
    apply le_antisymm
    · exact sup_le hRle hHle
    · intro g hgU
      have hginf : rho g pinf = pinf := by
        exact hgU
      have hgpzero_ne : rho g pzero ≠ pinf := by
        intro hbad
        apply hpzero_ne
        apply (rho g).injective
        exact hbad.trans hginf.symm
      rcases hRregular pzero (rho g pzero) hpzero_ne hgpzero_ne with
        ⟨r, hr, _⟩
      have hrU : (r : G) ∈ U := hRle r.property
      have hrinf : rho (r : G) pinf = pinf := by
        exact hrU
      let h : G := (r : G)⁻¹ * g
      have hhinf : rho h pinf = pinf := by
        change rho ((r : G)⁻¹ * g) pinf = pinf
        rw [map_mul, map_inv]
        change (rho (r : G))⁻¹ (rho g pinf) = pinf
        rw [hginf]
        calc
          (rho (r : G))⁻¹ pinf =
              (rho (r : G))⁻¹ (rho (r : G) pinf) := by rw [hrinf]
          _ = pinf := (rho (r : G)).symm_apply_apply pinf
      have hhzero : rho h pzero = pzero := by
        change rho ((r : G)⁻¹ * g) pzero = pzero
        rw [map_mul, map_inv]
        change (rho (r : G))⁻¹ (rho g pzero) = pzero
        calc
          (rho (r : G))⁻¹ (rho g pzero) =
              (rho (r : G))⁻¹ (rho (r : G) pzero) := by rw [hr]
          _ = pzero := (rho (r : G)).symm_apply_apply pzero
      have hhH : h ∈ H := hdoubleFix_mem_H h hhinf hhzero
      have hprod : (r : G) * h = g := by
        dsimp [h]
        group
      rw [← hprod]
      exact (R ⊔ H).mul_mem
        ((le_sup_left : R ≤ R ⊔ H) r.property)
        ((le_sup_right : H ≤ R ⊔ H) hhH)
  have hRnormal : U ≤ Subgroup.normalizer R := by
    rw [← hRsupH]
    exact sup_le Subgroup.le_normalizer hHnormal
  have hUstructure :
      U ≤ Subgroup.normalizer R ∧ R ⊓ H = ⊥ ∧ R ⊔ H = U := by
    exact ⟨hRnormal, hRinfH, hRsupH⟩
  rcases hUstructure with ⟨hRnormal, hRinfH, hRsupH⟩
  have hUcard : Nat.card U =
      q ^ 3 * (q ^ 2 - 1) / Nat.gcd (q + 1) 3 := by
    have hdisjRH : Disjoint R H := by
      rw [disjoint_iff_inf_le, hRinfH]
    have hdisj_sub : Disjoint (R.subgroupOf U) (H.subgroupOf U) := by
      rw [Subgroup.disjoint_def]
      intro x hxR hxH
      apply Subtype.ext
      exact Subgroup.disjoint_def.mp hdisjRH hxR hxH
    have hsup_sub : R.subgroupOf U ⊔ H.subgroupOf U = ⊤ := by
      simpa [hRsupH] using
        (Subgroup.subgroupOf_sup (A := R) (A' := H) (B := U) hRle hHle).symm
    letI : (R.subgroupOf U).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hRnormal
    have hcomp : (R.subgroupOf U).IsComplement' (H.subgroupOf U) := by
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj_sub ?_
      rw [Set.eq_univ_iff_forall]
      intro x
      have hx : x ∈ R.subgroupOf U ⊔ H.subgroupOf U := by simp [hsup_sub]
      rcases (Subgroup.mem_sup_of_normal_left
        (x := x) (s := R.subgroupOf U) (t := H.subgroupOf U)).1 hx with
        ⟨r, hr, h, hh, hmul⟩
      exact ⟨r, hr, h, hh, hmul⟩
    have hRsub_card : Nat.card (R.subgroupOf U) = Nat.card R :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (G := G) (H := R) (K := U) hRle).toEquiv
    have hHsub_card : Nat.card (H.subgroupOf U) = Nat.card H :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (G := G) (H := H) (K := U) hHle).toEquiv
    have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq q 1
    have hdq2 : Nat.gcd (q + 1) 3 ∣ q ^ 2 - 1 := by
      rw [hfactor]
      exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (q + 1) 3) _
    calc
      Nat.card U = q ^ 3 * ((q ^ 2 - 1) / Nat.gcd (q + 1) 3) := by
        simpa [hRsub_card, hHsub_card, hRcard, hHcard] using hcomp.card_mul.symm
      _ = q ^ 3 * (q ^ 2 - 1) / Nat.gcd (q + 1) 3 := by
        rw [← Nat.mul_div_assoc _ hdq2]
  have hstabilizer :
      ∃ (R H : Subgroup G),
        R ≤ U ∧ H ≤ U ∧ U ≤ Subgroup.normalizer R ∧
        R ⊓ H = ⊥ ∧ R ⊔ H = U ∧ IsCyclic H ∧
        Nat.card R = q ^ 3 ∧
        commutator R = Subgroup.center R ∧
        Nat.card (commutator R) = q ∧
        Nat.card H = (q ^ 2 - 1) / Nat.gcd (q + 1) 3 ∧
        (∀ a b : Omega, a ≠ pinf → b ≠ pinf →
          ∃! r : R, rho (r : G) a = b) ∧
        (∃ coordR :
            {z : K × K // z.2 + J.conj z.2 + z.1 * J.conj z.1 = 0} ≃ R,
          ∀ z : {z : K × K //
              z.2 + J.conj z.2 + z.1 * J.conj z.1 = 0},
            ∃ M : GL (Fin 3) K,
              (M : Matrix (Fin 3) (Fin 3) K) =
                !![1, (z : K × K).1, (z : K × K).2;
                   0, 1, -J.conj (z : K × K).1;
                   0, 0, 1] ∧
              ((((coordR z : R) : G) :
                Matrix.ProjGenLinGroup (Fin 3) K)) =
                  Matrix.ProjGenLinGroup.mk M) ∧
        (∀ h : H,
          ∃ k : Kˣ, ∃ M : GL (Fin 3) K,
            (M : Matrix (Fin 3) (Fin 3) K) =
              !![(J.conj (k : K))⁻¹, 0, 0;
                 0, J.conj (k : K) * (k : K)⁻¹, 0;
                 0, 0, (k : K)] ∧
            ((((h : H) : G) : Matrix.ProjGenLinGroup (Fin 3) K)) =
              Matrix.ProjGenLinGroup.mk M) ∧
        (∀ k : Kˣ,
          ∃ h : H, ∃ M : GL (Fin 3) K,
            (M : Matrix (Fin 3) (Fin 3) K) =
              !![(J.conj (k : K))⁻¹, 0, 0;
                 0, J.conj (k : K) * (k : K)⁻¹, 0;
                 0, 0, (k : K)] ∧
            ((((h : H) : G) : Matrix.ProjGenLinGroup (Fin 3) K)) =
              Matrix.ProjGenLinGroup.mk M) := by
    exact ⟨R, H, hRle, hHle, hRnormal, hRinfH, hRsupH, hHcyclic,
      hRcard, hRcomm, hRcomm_card, hHcard, hRregular, hRcoordinates,
      hHcoordinates, hHcoordinates_surjective⟩
  have htwo_transitive :
      ∀ a b c d : Omega, a ≠ b → c ≠ d →
        ∃ g : G, rho g a = c ∧ rho g b = d := by
    let weylG : G :=
      ⟨Matrix.ProjGenLinGroup.mk (hermitianWeylGL (K := K)),
        Subgroup.mem_map_of_mem Matrix.ProjGenLinGroup.mk
          (hermitianWeylSU J hJstandard).property⟩
    have hweyl_inf : rho weylG pinf = pzero := by
      apply Subtype.ext
      rw [hrho_apply weylG pinf (hermitianWeylSU J hJstandard) (by rfl)]
      rw [hOmegaEquiv.choose_spec.2 rootZero]
      rw [Projectivization.smul_mk]
      apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
      refine ⟨(1 : K), ?_⟩
      change (1 : K) • vaff rootZero =
        ((hermitianWeylGL (K := K) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K).mulVec vinf
      funext i
      fin_cases i <;>
        simp [vaff, vinf, rootZero, hermitianUnipotentOne,
          hermitianWeylGL, hermitianWeylMatrix, Matrix.mulVec]
    have hweyl_zero : rho weylG pzero = pinf := by
      apply Subtype.ext
      rw [hrho_apply weylG pzero (hermitianWeylSU J hJstandard) (by rfl)]
      rw [hOmegaEquiv.choose_spec.2 rootZero]
      rw [Projectivization.smul_mk]
      apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
      refine ⟨(1 : K), ?_⟩
      change (1 : K) • vinf =
        ((hermitianWeylGL (K := K) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K).mulVec (vaff rootZero)
      funext i
      fin_cases i <;>
        simp [vaff, vinf, rootZero, hermitianUnipotentOne,
          hermitianWeylGL, hermitianWeylMatrix, Matrix.mulVec]
    have hRfixInf (r : R) : rho (r : G) pinf = pinf := by
      exact hRle r.property
    have hpoint_to_inf : ∀ a : Omega, ∃ g : G, rho g a = pinf := by
      intro a
      by_cases ha : a = pinf
      · exact ⟨1, by simp [ha]⟩
      · rcases hRregular a pzero ha hpzero_ne with ⟨r, hr, _⟩
        refine ⟨weylG * (r : G), ?_⟩
        rw [map_mul]
        change rho weylG (rho (r : G) a) = pinf
        rw [hr, hweyl_zero]
    have hpair_to_standard :
        ∀ a b : Omega, a ≠ b →
          ∃ g : G, rho g a = pinf ∧ rho g b = pzero := by
      intro a b hab
      rcases hpoint_to_inf a with ⟨ga, hga⟩
      have hgb : rho ga b ≠ pinf := by
        intro hbad
        apply hab
        apply (rho ga).injective
        rw [hga, hbad]
      rcases hRregular (rho ga b) pzero hgb hpzero_ne with ⟨r, hr, _⟩
      refine ⟨(r : G) * ga, ?_, ?_⟩
      · rw [map_mul]
        change rho (r : G) (rho ga a) = pinf
        rw [hga]
        exact hRfixInf r
      · rw [map_mul]
        change rho (r : G) (rho ga b) = pzero
        exact hr
    intro a b c d hab hcd
    rcases hpair_to_standard a b hab with ⟨ga, hga, hgb⟩
    rcases hpair_to_standard c d hcd with ⟨gc, hgc, hgd⟩
    refine ⟨gc⁻¹ * ga, ?_, ?_⟩
    · rw [map_mul, map_inv]
      change (rho gc).symm (rho ga a) = c
      rw [hga]
      calc
        (rho gc).symm pinf = (rho gc).symm (rho gc c) :=
          congrArg (fun x => (rho gc).symm x) hgc.symm
        _ = c := (rho gc).symm_apply_apply c
    · rw [map_mul, map_inv]
      change (rho gc).symm (rho ga b) = d
      rw [hgb]
      calc
        (rho gc).symm pzero = (rho gc).symm (rho gc d) :=
          congrArg (fun x => (rho gc).symm x) hgd.symm
        _ = d := (rho gc).symm_apply_apply d
  have hGcard : Nat.card G =
      (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := by
    letI : MulAction G Omega := MulAction.compHom Omega rho
    have htwo' : MulAction.IsMultiplyPretransitive G Omega 2 := by
      rw [MulAction.is_two_pretransitive_iff]
      intro a b c d hab hcd
      exact htwo_transitive a b c d hab hcd
    letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwo'
    letI : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have hUeq : U = MulAction.stabilizer G pinf := rfl
    have hUindex : U.index = Nat.card Omega := by
      rw [hUeq]
      exact MulAction.index_stabilizer_of_transitive G pinf
    have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq q 1
    have hdq2 : Nat.gcd (q + 1) 3 ∣ q ^ 2 - 1 := by
      rw [hfactor]
      exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (q + 1) 3) _
    have hd : Nat.gcd (q + 1) 3 ∣ q ^ 3 * (q ^ 2 - 1) :=
      dvd_mul_of_dvd_right hdq2 _
    calc
      Nat.card G = Nat.card U * U.index := U.card_mul_index.symm
      _ = (q ^ 3 * (q ^ 2 - 1) / Nat.gcd (q + 1) 3) *
          (q ^ 3 + 1) := by rw [hUcard, hUindex, hpoints]
      _ = (q ^ 3 + 1) *
          (q ^ 3 * (q ^ 2 - 1) / Nat.gcd (q + 1) 3) := by ring
      _ = (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) /
          Nat.gcd 3 (q + 1) := by
        rw [← Nat.mul_div_assoc _ hd, Nat.gcd_comm]
        simp [mul_assoc]
  have hthree_fixed :
      2 < q →
        ∃ g : G, g ≠ 1 ∧
          ∃ a b c : Omega,
            a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
              rho g a = a ∧ rho g b = b ∧ rho g c = c := by
    intro hq2
    have hcardUnits : Nat.card Kˣ = q ^ 2 - 1 := by
      rw [Nat.card_units, hKcard]
    have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq q 1
    have hdq1 : q + 1 ∣ q ^ 2 - 1 := by
      rw [hfactor]
      exact dvd_mul_left (q + 1) (q - 1)
    have hnormRootsCard :
        Nat.card (rootsOfUnity (q + 1) K) = q + 1 := by
      letI : IsCyclic Kˣ := inferInstance
      rw [rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker,
        hcardUnits, Nat.gcd_eq_right hdq1]
    have hthree_lt :
        3 < Nat.card (rootsOfUnity (q + 1) K) := by
      rw [hnormRootsCard]
      omega
    letI : IsCyclic (rootsOfUnity (q + 1) K) := inferInstance
    obtain ⟨k, hkthree⟩ :=
      exists_pow_ne_one_of_isCyclic (G := rootsOfUnity (q + 1) K)
        (by decide : (3 : ℕ) ≠ 0) hthree_lt
    let ku : Kˣ := (k : Kˣ)
    have hkqUnits : ku ^ (q + 1) = 1 := by
      exact (mem_rootsOfUnity (q + 1) (k : Kˣ)).mp k.property
    have hkq : (ku : K) ^ (q + 1) = 1 := by
      simpa using congrArg Units.val hkqUnits
    have hg_ne : torusG ku ≠ 1 := by
      intro hg
      have hkern : ku ∈ torusHom.ker := MonoidHom.mem_ker.mpr hg
      have hkcube : (ku : K) ^ 3 = 1 :=
        (htorusMemKerIff ku).mp hkern |>.2
      apply hkthree
      apply Subtype.ext
      apply Units.ext
      simpa [ku] using hkcube
    have hconjpow : J.conj (ku : K) = (ku : K) ^ q :=
      huppert_II_10_4_conj_eq_frobenius
        J q hKcard hfixed_card (ku : K)
    have hnorm : J.conj (ku : K) * (ku : K) = 1 := by
      rw [hconjpow]
      simpa [pow_succ] using hkq
    have houter : (J.conj (ku : K))⁻¹ = (ku : K) := by
      calc
        (J.conj (ku : K))⁻¹ =
            (J.conj (ku : K))⁻¹ *
              (J.conj (ku : K) * (ku : K)) := by rw [hnorm, mul_one]
        _ = ((J.conj (ku : K))⁻¹ * J.conj (ku : K)) *
            (ku : K) := by ring
        _ = (ku : K) := by
          rw [inv_mul_cancel₀
            ((map_ne_zero J.conj).2 (Units.ne_zero ku)), one_mul]
    obtain ⟨u, hu⟩ := hnonfixed
    let delta : K := u - J.conj u
    have hdelta_ne : delta ≠ 0 := by
      exact sub_ne_zero.mpr hu.symm
    have hdelta_trace : delta + J.conj delta = 0 := by
      dsimp [delta]
      rw [map_sub, J.conj_involutive]
      ring
    let zthird : S := ⟨((0 : K), delta), by
      simpa using hdelta_trace⟩
    have hzthird_ne_zero : zthird ≠ rootZero := by
      intro hz
      apply hdelta_ne
      have h := congrArg (fun z : S => (z : K × K).2) hz
      simpa [zthird, rootZero, hermitianUnipotentOne] using h
    let pthird : Omega := hOmegaEquiv.choose.symm (some zthird)
    have hthird_ne_inf : pthird ≠ pinf := by
      intro h
      have heq := congrArg hOmegaEquiv.choose h
      rw [hOmegaEquiv.choose.apply_symm_apply,
        hOmegaEquiv.choose_spec.1] at heq
      contradiction
    have hthird_ne_zero : pthird ≠ pzero := by
      intro h
      apply hzthird_ne_zero
      apply Option.some.inj
      apply hOmegaEquiv.choose.symm.injective
      exact h
    have hfix_inf : rho (torusG ku) pinf = pinf := by
      apply Subtype.ext
      rw [hrho_apply (torusG ku) pinf
        (hermitianTorusSU J hJstandard ku) (by rfl)]
      change
        (Matrix.GeneralLinearGroup.toLin (torusGL ku)).toLinearEquiv •
            Projectivization.mk K vinf hvinf =
          Projectivization.mk K vinf hvinf
      rw [Projectivization.smul_mk]
      apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
      refine ⟨(J.conj (ku : K))⁻¹, ?_⟩
      change (J.conj (ku : K))⁻¹ • vinf =
        (torusGL ku : Matrix (Fin 3) (Fin 3) K).mulVec vinf
      rw [htorusGLVal]
      funext i
      fin_cases i <;>
        simp [torusMatrix, hermitianTorusMatrix, vinf, Matrix.mulVec]
    have hfix_affine :
        ∀ z : S, (z : K × K).1 = 0 →
          rho (torusG ku) (hOmegaEquiv.choose.symm (some z)) =
            hOmegaEquiv.choose.symm (some z) := by
      intro z hz
      apply Subtype.ext
      rw [hrho_apply (torusG ku) (hOmegaEquiv.choose.symm (some z))
        (hermitianTorusSU J hJstandard ku) (by rfl)]
      rw [hOmegaEquiv.choose_spec.2 z]
      rw [Projectivization.smul_mk]
      apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
      refine ⟨(ku : K), ?_⟩
      change (ku : K) • vaff z =
        (torusGL ku : Matrix (Fin 3) (Fin 3) K).mulVec (vaff z)
      rw [htorusGLVal]
      funext i
      fin_cases i <;>
        simp [torusMatrix, hermitianTorusMatrix, vaff, hz, houter,
          Matrix.mulVec]
    have hfix_zero : rho (torusG ku) pzero = pzero := by
      exact hfix_affine rootZero (by
        simp [rootZero, hermitianUnipotentOne])
    have hfix_third : rho (torusG ku) pthird = pthird := by
      exact hfix_affine zthird (by simp [zthird])
    refine ⟨torusG ku, hg_ne, pinf, pzero, pthird,
      hpzero_ne.symm, hthird_ne_inf.symm, hthird_ne_zero.symm,
      hfix_inf, hfix_zero, hfix_third⟩
  refine ⟨hpoints, rho, pinf, hrho, hrho_apply, ?_⟩
  change Nat.card U = q ^ 3 * (q ^ 2 - 1) / Nat.gcd (q + 1) 3 ∧
    (∃ (R H : Subgroup G),
      R ≤ U ∧ H ≤ U ∧ U ≤ Subgroup.normalizer R ∧
      R ⊓ H = ⊥ ∧ R ⊔ H = U ∧ IsCyclic H ∧
      Nat.card R = q ^ 3 ∧
      commutator R = Subgroup.center R ∧
      Nat.card (commutator R) = q ∧
      Nat.card H = (q ^ 2 - 1) / Nat.gcd (q + 1) 3 ∧
      (∀ a b : Omega, a ≠ pinf → b ≠ pinf →
        ∃! r : R, rho (r : G) a = b) ∧
      (∃ coordR :
          {z : K × K // z.2 + J.conj z.2 + z.1 * J.conj z.1 = 0} ≃ R,
        ∀ z : {z : K × K //
            z.2 + J.conj z.2 + z.1 * J.conj z.1 = 0},
          ∃ M : GL (Fin 3) K,
            (M : Matrix (Fin 3) (Fin 3) K) =
              !![1, (z : K × K).1, (z : K × K).2;
                 0, 1, -J.conj (z : K × K).1;
                 0, 0, 1] ∧
            ((((coordR z : R) : G) :
              Matrix.ProjGenLinGroup (Fin 3) K)) =
                Matrix.ProjGenLinGroup.mk M) ∧
      (∀ h : H,
        ∃ k : Kˣ, ∃ M : GL (Fin 3) K,
          (M : Matrix (Fin 3) (Fin 3) K) =
            !![(J.conj (k : K))⁻¹, 0, 0;
               0, J.conj (k : K) * (k : K)⁻¹, 0;
               0, 0, (k : K)] ∧
          ((((h : H) : G) : Matrix.ProjGenLinGroup (Fin 3) K)) =
            Matrix.ProjGenLinGroup.mk M) ∧
      (∀ k : Kˣ,
        ∃ h : H, ∃ M : GL (Fin 3) K,
          (M : Matrix (Fin 3) (Fin 3) K) =
            !![(J.conj (k : K))⁻¹, 0, 0;
               0, J.conj (k : K) * (k : K)⁻¹, 0;
               0, 0, (k : K)] ∧
          ((((h : H) : G) : Matrix.ProjGenLinGroup (Fin 3) K)) =
            Matrix.ProjGenLinGroup.mk M)) ∧
    (∀ a b c d : Omega, a ≠ b → c ≠ d →
      ∃ g : G, rho g a = c ∧ rho g b = d) ∧
    Nat.card G =
      (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) ∧
    (2 < q →
      ∃ g : G, g ≠ 1 ∧
        ∃ a b c : Omega,
          a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
            rho g a = a ∧ rho g b = b ∧ rho g c = c)
  exact ⟨hUcard, hstabilizer, htwo_transitive, hGcard, hthree_fixed⟩

end External
end CFSG.BenderSuzuki
