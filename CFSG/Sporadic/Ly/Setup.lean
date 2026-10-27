module

public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Certificates.SchreierStabilizerGenerators
public import CFSG.Sporadic.Schreier.LyCheckOrbit
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Ly.KeySpec

public section

namespace CFSG.Sporadic.Ly

open Native Matrix
open CFSG.Sporadic.He.Native (toMat toMat_mulM toMat_idM toMat_powM toMat_rowsOf toMat_eq_of_beq
  mulM powM idM)

noncomputable abbrev mA : Matrix (Fin 111) (Fin 111) (ZMod 5) :=
  Blueprint.NativeSporadic.decode 5 111 1 Blueprint.NativeSporadic.LySeed1

noncomputable abbrev mB : Matrix (Fin 111) (Fin 111) (ZMod 5) :=
  Blueprint.NativeSporadic.decode 5 111 1 Blueprint.NativeSporadic.LySeed2

noncomputable abbrev mF : Matrix (Fin 111) (Fin 111) (ZMod 5) := toMat 5 111 formF

private theorem seedA_eq' : seedA = Blueprint.NativeSporadic.LySeed1 := rfl

private theorem seedB_eq' : seedB = Blueprint.NativeSporadic.LySeed2 := rfl

theorem toMat_matA : toMat 5 111 matA = mA := by
  unfold matA; rw [toMat_rowsOf, seedA_eq']

theorem toMat_matB : toMat 5 111 matB = mB := by
  unfold matB; rw [toMat_rowsOf, seedB_eq']

noncomputable abbrev mX : Matrix (Fin 111) (Fin 111) (ZMod 5) :=
  mA * ((mB * mA) * (mB * mA)) * mB * ((mA * mB ^ 4) * (mA * mB ^ 4))

theorem toMat_matX : toMat 5 111 matX = mX := by
  unfold matX matG matGi
  simp only [toMat_mulM, toMat_powM, toMat_matA, toMat_matB]

end CFSG.Sporadic.Ly

namespace CFSG.Sporadic.LySchreier

@[expose] def lyF : Matrix (Fin 111) (Fin 111) (ZMod 5) :=
  CFSG.Sporadic.He.Native.toMat 5 111 Native.bpForm

end CFSG.Sporadic.LySchreier

namespace CFSG.Sporadic.Ly

open Native Matrix
open CFSG.Sporadic.He.Native (toMat)
open CFSG.Sporadic.LySchreier (lyF)

class LySeed : Prop where
  mA_sq : mA * mA = 1
  mB_pow : mB ^ 5 = 1
  mX_pow : mX ^ 67 = 1
  form_A : mAᵀ * lyF * mA = lyF
  form_B : mBᵀ * lyF * mB = lyF

theorem mA_sq [LySeed] : mA * mA = 1 := LySeed.mA_sq

theorem mB_pow [LySeed] : mB ^ 5 = 1 := LySeed.mB_pow

theorem mX_pow [LySeed] : mX ^ 67 = 1 := LySeed.mX_pow

theorem form_A [LySeed] : mAᵀ * lyF * mA = lyF := LySeed.form_A

theorem form_B [LySeed] : mBᵀ * lyF * mB = lyF := LySeed.form_B

theorem det_mB [LySeed] : mB.det = 1 := by
  have h := congrArg Matrix.det mB_pow
  rwa [Matrix.det_pow, Matrix.det_one, ZMod.pow_card] at h

theorem det_mA [LySeed] : mA.det = 1 := by
  have h2 : mA.det * mA.det = 1 := by
    have := congrArg Matrix.det mA_sq
    rwa [Matrix.det_mul, Matrix.det_one] at this
  have hX : mX.det = mA.det ^ 5 := by
    simp only [mX, Matrix.det_mul, Matrix.det_pow, det_mB, one_pow, mul_one]
    ring
  have h67 : mX.det ^ 67 = 1 := by rw [← Matrix.det_pow, mX_pow, Matrix.det_one]
  calc mA.det = (mA.det * mA.det) ^ 167 * mA.det := by rw [h2, one_pow, one_mul]
    _ = (mA.det ^ 5) ^ 67 := by ring
    _ = 1 := by rw [← hX, h67]

theorem det_mA_ne_zero
    [LySeed] : mA.det ≠ 0 := by rw [det_mA]; exact one_ne_zero

theorem det_mB_ne_zero
    [LySeed] : mB.det ≠ 0 := by rw [det_mB]; exact one_ne_zero

noncomputable abbrev gA [LySeed] : GL (Fin 111) (ZMod 5) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mA det_mA_ne_zero

noncomputable abbrev gB [LySeed] : GL (Fin 111) (ZMod 5) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mB det_mB_ne_zero

noncomputable abbrev J
    [LySeed] : Subgroup (GL (Fin 111) (ZMod 5)) := Subgroup.closure {gA, gB}

@[expose] noncomputable def a
    [LySeed] : J := ⟨gA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def b
    [LySeed] : J := ⟨gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

noncomputable abbrev mat [LySeed]
    (g : J) : Matrix (Fin 111) (Fin 111) (ZMod 5) :=
  ((g : GL (Fin 111) (ZMod 5)) : Matrix (Fin 111) (Fin 111) (ZMod 5))

theorem mat_mul [LySeed] (g h : J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one [LySeed] : mat (1 : J) = 1 := rfl

theorem mat_injective [LySeed] : Function.Injective mat := by
  intro g h e
  exact Subtype.ext (Units.ext e)

theorem mat_a [LySeed] : mat a = mA := rfl

theorem mat_b [LySeed] : mat b = mB := rfl

theorem closure_ab [LySeed] : Subgroup.closure ({a, b} : Set J) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    ({gA, gB} : Set (GL (Fin 111) (ZMod 5)))
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl) <;> simp [a, b]
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

noncomputable def lyEquivJ [LySeed] : Blueprint.NativeSporadic.Ly ≃* J :=
  Blueprint.NativeSporadic.matrixSeedEquiv 5 111 (by norm_num) mA mB det_mA_ne_zero
    det_mB_ne_zero

theorem det_and_form [LySeed]
    (g : J) : (mat g).det = 1 ∧ (mat g)ᵀ * lyF * mat g = lyF := by
  have hg : g ∈ Subgroup.closure ({a, b} : Set J) := by rw [closure_ab]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨det_mA, form_A⟩
    · exact ⟨det_mB, form_B⟩
  | one => simp [mat_one]
  | mul x y _ _ hx hy =>
    refine ⟨by rw [mat_mul, Matrix.det_mul, hx.1, hy.1, mul_one], ?_⟩
    rw [mat_mul, Matrix.transpose_mul]
    calc (mat y)ᵀ * (mat x)ᵀ * lyF * (mat x * mat y) =
          (mat y)ᵀ * ((mat x)ᵀ * lyF * mat x) * mat y := by simp only [Matrix.mul_assoc]
      _ = lyF := by rw [hx.2, hy.2]
  | inv x _ hx =>
    have hinv : mat x⁻¹ * mat x = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
    have hinv' : mat x * mat x⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
    refine ⟨?_, ?_⟩
    · have := congrArg Matrix.det hinv
      rw [Matrix.det_mul, hx.1, mul_one, Matrix.det_one] at this
      exact this
    · calc (mat x⁻¹)ᵀ * lyF * mat x⁻¹ =
            (mat x⁻¹)ᵀ * ((mat x)ᵀ * lyF * mat x) * mat x⁻¹ := by rw [hx.2]
        _ = (mat x * mat x⁻¹)ᵀ * lyF * (mat x * mat x⁻¹) := by
            rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
        _ = lyF := by rw [hinv', Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

end CFSG.Sporadic.Ly
