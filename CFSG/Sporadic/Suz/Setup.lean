
module

public import CFSG.Sporadic.Suz.SetupBase
import all CFSG.Sporadic.Suz.SetupBase

public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Certificates.SchreierStabilizerGenerators
public import CFSG.Sporadic.Suz.Certificate
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Suz

open CFSG.F3.Native Native Matrix CFSG.Sporadic.VecOrbit

section Facts

variable (hM : MatrixFacts)
include hM

end Facts

theorem certificate_parts : matrixChecks = true ∧ formChecks = true ∧
    conjOrbitOKW 64 wRoot wA wA wB wBi orb 3 = true ∧ actionChecks orb 3 = true := by
  have h := suz_certificate
  unfold suzCertificate at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem matrixFacts :
    MatrixFacts := matrixFacts_of certificate_parts.1

theorem det_seeds :
    mA.det = 1 ∧ mB.det = 1 := ⟨det_mA matrixFacts, det_mB matrixFacts⟩

noncomputable abbrev gA : GL (Fin 64) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mA (det_mA_ne_zero matrixFacts)

noncomputable abbrev gB : GL (Fin 64) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mB (det_mB_ne_zero matrixFacts)

noncomputable abbrev J :
    Subgroup (GL (Fin 64) (ZMod 3)) := Subgroup.closure {gA, gB}

@[expose] noncomputable def a :
    J := ⟨gA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def b :
    J := ⟨gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem a_val : ((a : GL (Fin 64) (ZMod 3)) : Matrix (Fin 64) (Fin 64) (ZMod 3)) = mA := rfl

theorem b_val : ((b : GL (Fin 64) (ZMod 3)) : Matrix (Fin 64) (Fin 64) (ZMod 3)) = mB := rfl

theorem closure_ab : Subgroup.closure ({a, b} : Set J) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    ({gA, gB} : Set (GL (Fin 64) (ZMod 3)))
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl) <;> simp [a, b]
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

noncomputable def suzEquivJ : Blueprint.NativeSporadic.Suz ≃* J :=
  Blueprint.NativeSporadic.matrixSeedEquiv 3 64 (by norm_num) mA mB (det_mA_ne_zero matrixFacts)
    (det_mB_ne_zero matrixFacts)

noncomputable abbrev mat
    (g : J) : Matrix (Fin 64) (Fin 64) (ZMod 3) :=
  ((g : GL (Fin 64) (ZMod 3)) : Matrix (Fin 64) (Fin 64) (ZMod 3))

theorem mat_mul (g h : J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : J) = 1 := rfl

theorem mat_injective : Function.Injective mat := by
  intro g h e
  exact Subtype.ext (Units.ext e)

theorem mat_pow (g : J) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  simp [mat, Units.val_pow_eq_pow_val]

theorem mat_a : mat a = toMat 64 matA := by rw [toMat_matA]; rfl

theorem mat_b : mat b = toMat 64 matB := by rw [toMat_matB]; rfl

theorem a_sq : a ^ 2 = 1 := by
  apply mat_injective
  rw [mat_pow, mat_one, mat_a, toMat_matA, pow_two]
  exact matrixFacts.A_sq

theorem a_ne_one : a ≠ 1 := by
  intro h
  apply matrixFacts.A_ne
  have := congrArg mat h
  rwa [mat_a, toMat_matA, mat_one] at this

theorem b_cube : b ^ 3 = 1 := by
  apply mat_injective
  rw [mat_pow, mat_one, mat_b, toMat_matB]
  exact matrixFacts.B_cube

theorem b_ne_one : b ≠ 1 := by
  intro h
  apply matrixFacts.B_ne
  have := congrArg mat h
  rwa [mat_b, toMat_matB, mat_one] at this

theorem ab_pow : (a * b) ^ 13 = 1 := by
  apply mat_injective
  rw [mat_pow, mat_one, mat_mul, mat_a, mat_b, toMat_matA, toMat_matB]
  exact matrixFacts.AB_pow

theorem ab_ne_one : a * b ≠ 1 := by
  intro h
  apply matrixFacts.AB_ne
  have := congrArg mat h
  rwa [mat_mul, mat_a, mat_b, toMat_matA, toMat_matB, mat_one] at this

theorem a_inv : a⁻¹ = a := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, a_sq]

theorem b_inv : b⁻¹ = b * b := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, ← pow_succ', b_cube]

end CFSG.Sporadic.Suz
