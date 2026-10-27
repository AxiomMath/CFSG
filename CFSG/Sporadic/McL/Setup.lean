module

public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.McL.VecSpec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import CFSG.Sporadic.McL.Certificate
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.McL

open CFSG.F3.Native Native Matrix CFSG.Sporadic.VecOrbit

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable abbrev mA : Matrix (Fin 21) (Fin 21) (ZMod 3) :=
  Blueprint.NativeSporadic.decode 3 21 1 Blueprint.NativeSporadic.McLSeed1

noncomputable abbrev mB : Matrix (Fin 21) (Fin 21) (ZMod 3) :=
  Blueprint.NativeSporadic.decode 3 21 1 Blueprint.NativeSporadic.McLSeed2

private theorem seedA_eq' : seedA = Blueprint.NativeSporadic.McLSeed1 := rfl

private theorem seedB_eq' : seedB = Blueprint.NativeSporadic.McLSeed2 := rfl

theorem seedA_eq : seedA = Blueprint.NativeSporadic.McLSeed1 := seedA_eq'

theorem seedB_eq : seedB = Blueprint.NativeSporadic.McLSeed2 := seedB_eq'

theorem toMat_matA : toMat 21 matA = mA := by
  unfold matA; rw [toMat_rowsOf, seedA_eq]

theorem toMat_matB : toMat 21 matB = mB := by
  unfold matB; rw [toMat_rowsOf, seedB_eq]

theorem matA_size : matA.size = 21 := by unfold matA rowsOf; simp

theorem matB_size : matB.size = 21 := by unfold matB rowsOf; simp

theorem rowsWF_matA : RowsWF matA := RowsWF.rowsOf 21 seedA

theorem rowsWF_matB : RowsWF matB := RowsWF.rowsOf 21 seedB

structure MatrixFacts : Prop where
  A_sq : mA * mA = 1
  B_pow : mB ^ 5 = 1
  AB_pow : (mA * mB) ^ 11 = 1
  A_ne : mA ≠ 1
  B_ne : mB ≠ 1
  AB_ne : mA * mB ≠ 1

theorem matrixFacts_of (h : matrixChecks = true) : MatrixFacts := by
  unfold matrixChecks at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hAc, hBc⟩, hIc⟩, hABc⟩, hA2⟩, hB5⟩, hAB11⟩, hA1⟩, hB1⟩, hAB1⟩ := h
  have hAB_size : (mul 21 matA matB).size = 21 := by rw [mul_size, matA_size]
  have hABwf : RowsWF (mul 21 matA matB) := RowsWF.mul _ 21 rowsWF_matA rowsWF_matB
  have htAB : toMat 21 (mul 21 matA matB) = mA * mB := by
    rw [toMat_mul matA_size rowsWF_matA rowsWF_matB, toMat_matA, toMat_matB]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := toMat_eq_of_eqM hA2
    rwa [toMat_mul matA_size rowsWF_matA rowsWF_matA, toMat_idM, toMat_matA] at this
  · have := toMat_eq_of_eqM hB5
    rwa [toMat_powM rowsWF_matB, toMat_idM, toMat_matB] at this
  · have := toMat_eq_of_eqM hAB11
    rwa [toMat_powM hABwf, toMat_idM, htAB] at this
  · have := not_eqM_of_ne matA_size hA1 hAc hIc
    rwa [toMat_idM, toMat_matA] at this
  · have := not_eqM_of_ne matB_size hB1 hBc hIc
    rwa [toMat_idM, toMat_matB] at this
  · have := not_eqM_of_ne hAB_size hAB1 hABc hIc
    rwa [toMat_idM, htAB] at this

private theorem zmod3_pow5_eq_one : ∀ x : ZMod 3, x ^ 5 = 1 → x = 1 := by decide

private theorem zmod3_pow11_eq_one : ∀ x : ZMod 3, x ^ 11 = 1 → x = 1 := by decide

section Facts

variable (hM : MatrixFacts)
include hM

theorem det_mB : mB.det = 1 := by
  apply zmod3_pow5_eq_one
  rw [← Matrix.det_pow, hM.B_pow, Matrix.det_one]

theorem det_mA : mA.det = 1 := by
  have h : (mA * mB).det = 1 := by
    apply zmod3_pow11_eq_one
    rw [← Matrix.det_pow, hM.AB_pow, Matrix.det_one]
  rwa [Matrix.det_mul, det_mB hM, mul_one] at h

theorem det_mA_ne_zero : mA.det ≠ 0 := by rw [det_mA hM]; exact one_ne_zero

theorem det_mB_ne_zero : mB.det ≠ 0 := by rw [det_mB hM]; exact one_ne_zero

end Facts

@[expose] noncomputable def orb : VecOrbit.Native.VOrbit := orbitData ()

theorem certificate_parts : matrixChecks = true ∧
    VecOrbit.Native.vecOrbitOK 21 (transpose 21 matA) (transpose 21 matB) orb 3 = true ∧
    actionChecks orb 3 = true := by
  have h := mcl_certificate
  unfold mclCertificate at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem matrixFacts :
    MatrixFacts := matrixFacts_of certificate_parts.1

theorem det_seeds :
    mA.det = 1 ∧ mB.det = 1 := ⟨det_mA matrixFacts, det_mB matrixFacts⟩

noncomputable abbrev gA : GL (Fin 21) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mA (det_mA_ne_zero matrixFacts)

noncomputable abbrev gB : GL (Fin 21) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mB (det_mB_ne_zero matrixFacts)

noncomputable abbrev J :
    Subgroup (GL (Fin 21) (ZMod 3)) := Subgroup.closure {gA, gB}

@[expose] noncomputable def a :
    J := ⟨gA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def b :
    J := ⟨gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem a_val : ((a : GL (Fin 21) (ZMod 3)) : Matrix (Fin 21) (Fin 21) (ZMod 3)) = mA := rfl

theorem b_val : ((b : GL (Fin 21) (ZMod 3)) : Matrix (Fin 21) (Fin 21) (ZMod 3)) = mB := rfl

theorem closure_ab : Subgroup.closure ({a, b} : Set J) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    ({gA, gB} : Set (GL (Fin 21) (ZMod 3)))
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl) <;> simp [a, b]
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

noncomputable def mclEquivJ : Blueprint.NativeSporadic.McL ≃* J :=
  Blueprint.NativeSporadic.matrixSeedEquiv 3 21 (by norm_num) mA mB (det_mA_ne_zero matrixFacts)
    (det_mB_ne_zero matrixFacts)

noncomputable abbrev mat
    (g : J) : Matrix (Fin 21) (Fin 21) (ZMod 3) :=
  ((g : GL (Fin 21) (ZMod 3)) : Matrix (Fin 21) (Fin 21) (ZMod 3))

theorem mat_mul (g h : J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : J) = 1 := rfl

theorem mat_injective : Function.Injective mat := by
  intro g h e
  exact Subtype.ext (Units.ext e)

theorem mat_a : mat a = toMat 21 matA := by rw [toMat_matA]; rfl

theorem mat_b : mat b = toMat 21 matB := by rw [toMat_matB]; rfl

theorem mat_pow (g : J) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  simp [mat, Units.val_pow_eq_pow_val]

end CFSG.Sporadic.McL
