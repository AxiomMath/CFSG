
module

public import CFSG.Sporadic.ON.SetupBase
import all CFSG.Sporadic.ON.SetupBase

public import CFSG.Sporadic.ON.Certificate
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Certificates.SchreierStabilizerGenerators
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.ON

open Native Matrix
open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native
open CFSG.Sporadic.SmallF2.Native (lettersOf instrLt ordOK inTreeB labelsOf)

theorem facts : Facts := by
  have h := on_certificate
  unfold onCertificate at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem mA_sq : mA * mA = 1 := by
  have h := facts.matrix
  unfold matrixChecks at h
  simp only [Bool.and_eq_true] at h
  have e := toMat_eq_of_eqM h.1
  rwa [toMat_mul rowsA_size rowsWF_rowsA rowsWF_rowsA, toMat_idM, toMat_rowsA] at e

theorem mB_pow : mB ^ 4 = 1 := by
  have h := facts.matrix
  unfold matrixChecks at h
  simp only [Bool.and_eq_true] at h
  have e := toMat_eq_of_eqM h.2
  rwa [(powM_facts rowsWF_rowsB 4).2.2, toMat_idM, toMat_rowsB] at e

theorem det_mA_ne_zero : mA.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det mA_sq
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem det_mB_ne_zero : mB.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det mB_pow
  rw [Matrix.det_pow, h, Matrix.det_one, zero_pow (by norm_num)] at this
  exact zero_ne_one this

noncomputable abbrev gA : GL (Fin 154) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mA det_mA_ne_zero

noncomputable abbrev gB : GL (Fin 154) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mB det_mB_ne_zero

noncomputable abbrev J :
    Subgroup (GL (Fin 154) (ZMod 3)) := Subgroup.closure {gA, gB}

@[expose] noncomputable def ga :
    J := ⟨gA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def gb : J :=
  ⟨gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

noncomputable abbrev mat
    (g : J) : Matrix (Fin 154) (Fin 154) (ZMod 3) :=
  ((g : GL (Fin 154) (ZMod 3)) : Matrix (Fin 154) (Fin 154) (ZMod 3))

theorem mat_mul (g h : J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : J) = 1 := rfl

theorem mat_injective : Function.Injective mat := by
  intro g h e
  exact Subtype.ext (Units.ext e)

theorem mat_ga : mat ga = mA := rfl

theorem mat_gb : mat gb = mB := rfl

theorem closure_gab : Subgroup.closure ({ga, gb} : Set J) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    ({gA, gB} : Set (GL (Fin 154) (ZMod 3)))
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl) <;> simp [ga, gb]
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

noncomputable def onEquivJ : Blueprint.NativeSporadic.ON ≃* J :=
  Blueprint.NativeSporadic.matrixSeedEquiv 3 154 (by norm_num) mA mB det_mA_ne_zero
    det_mB_ne_zero

theorem mat_onEquivJ
    (u : Blueprint.NativeSporadic.ON) : mat (onEquivJ u) = u.val.val :=
  Blueprint.NativeSporadic.matrixSeedEquiv_val 3 154 (by norm_num) mA mB det_mA_ne_zero
    det_mB_ne_zero u

end CFSG.Sporadic.ON
