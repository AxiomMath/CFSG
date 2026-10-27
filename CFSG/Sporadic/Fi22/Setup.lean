module

public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.F3.ConjSpec
public import CFSG.F3.SepSpec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import CFSG.Sporadic.Fi22.Certificate
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Fi22

open CFSG.F3.Native Native Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable abbrev mA : Matrix (Fin 77) (Fin 77) (ZMod 3) :=
  Blueprint.NativeSporadic.decode 3 77 1 Blueprint.NativeSporadic.Fi22Seed1

noncomputable abbrev mB : Matrix (Fin 77) (Fin 77) (ZMod 3) :=
  Blueprint.NativeSporadic.decode 3 77 1 Blueprint.NativeSporadic.Fi22Seed2

private theorem seedA_eq' : seedA = Blueprint.NativeSporadic.Fi22Seed1 := rfl

private theorem seedB_eq' : seedB = Blueprint.NativeSporadic.Fi22Seed2 := rfl

theorem seedA_eq : seedA = Blueprint.NativeSporadic.Fi22Seed1 := seedA_eq'

theorem seedB_eq : seedB = Blueprint.NativeSporadic.Fi22Seed2 := seedB_eq'

theorem toMat_matA : toMat 77 matA = mA := by
  unfold matA; rw [toMat_rowsOf, seedA_eq]

theorem toMat_matB : toMat 77 matB = mB := by
  unfold matB; rw [toMat_rowsOf, seedB_eq]

theorem matA_size : matA.size = 77 := by unfold matA rowsOf; simp

theorem matB_size : matB.size = 77 := by unfold matB rowsOf; simp

theorem rowsWF_matA : RowsWF matA := RowsWF.rowsOf 77 seedA

theorem rowsWF_matB : RowsWF matB := RowsWF.rowsOf 77 seedB

theorem powM_size (d : ℕ) (M : Array V) (e : ℕ) : (powM d M e).size = d := by
  induction e with
  | zero => exact idM_size d
  | succ e ih => rw [powM, mul_size, ih]

theorem RowsWF.powM {d : ℕ} {M : Array V} (hM : RowsWF M) (e : ℕ) : RowsWF (powM d M e) := by
  induction e with
  | zero => exact RowsWF.idM d
  | succ e ih => exact RowsWF.mul _ d ih hM

theorem toMat_powM {d : ℕ} {M : Array V} (hM : RowsWF M) (e : ℕ) :
    toMat d (powM d M e) = toMat d M ^ e := by
  induction e with
  | zero => rw [pow_zero]; exact toMat_idM d
  | succ e ih =>
    rw [CFSG.F3.Native.powM, toMat_mul (powM_size d M e) (RowsWF.powM hM e) hM, ih, pow_succ]

theorem matBi_size : matBi.size = 77 := powM_size 77 matB 12

theorem rowsWF_matBi : RowsWF matBi := RowsWF.powM rowsWF_matB 12

structure MatrixFacts : Prop where
  A_sq : mA * mA = 1
  B_inv : mB * toMat 77 matBi = 1
  B_pow : mB ^ 13 = 1
  AB_pow : (mA * mB) ^ 11 = 1
  A_ne : mA ≠ 1
  B_ne : mB ≠ 1
  AB_ne : mA * mB ≠ 1

theorem not_eqM_of_ne {X Y : Array V} (hX : X.size = 77) (hY : Y.size = 77)
    (h : eqM 77 X Y = false) : canonM 77 X = true → canonM 77 Y = true →
      toMat 77 X ≠ toMat 77 Y := by
  intro hXc hYc he
  have := eq_of_canonM hXc hYc he
  subst this
  unfold eqM at h
  simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne] at h
  rcases h with (h | h) | h
  · exact h hX
  · exact h hX
  · rw [Nat.all_eq_finRange_all, List.all_eq_false] at h
    obtain ⟨i, -, hi⟩ := h
    simp [V.beq] at hi

theorem matrixFacts_of (h : matrixChecks = true) : MatrixFacts := by
  unfold matrixChecks at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hAc, hBc⟩, hIc⟩, hABc⟩, hA2⟩, hBBi⟩, hB13⟩, hAB11⟩, hA1⟩, hB1⟩, hAB1⟩ := h
  have hAB_size : (mul 77 matA matB).size = 77 := by rw [mul_size, matA_size]
  have hABwf : RowsWF (mul 77 matA matB) := RowsWF.mul _ 77 rowsWF_matA rowsWF_matB
  have htAB : toMat 77 (mul 77 matA matB) = mA * mB := by
    rw [toMat_mul matA_size rowsWF_matA rowsWF_matB, toMat_matA, toMat_matB]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := toMat_eq_of_eqM hA2
    rwa [toMat_mul matA_size rowsWF_matA rowsWF_matA, toMat_idM, toMat_matA] at this
  · have := toMat_eq_of_eqM hBBi
    rwa [toMat_mul matB_size rowsWF_matB rowsWF_matBi, toMat_idM, toMat_matB] at this
  · have := toMat_eq_of_eqM hB13
    rwa [toMat_powM rowsWF_matB, toMat_idM, toMat_matB] at this
  · have := toMat_eq_of_eqM hAB11
    rwa [toMat_powM hABwf, toMat_idM, htAB] at this
  · have := not_eqM_of_ne matA_size (idM_size 77) hA1 hAc hIc
    rwa [toMat_idM, toMat_matA] at this
  · have := not_eqM_of_ne matB_size (idM_size 77) hB1 hBc hIc
    rwa [toMat_idM, toMat_matB] at this
  · have := not_eqM_of_ne hAB_size (idM_size 77) hAB1 hABc hIc
    rwa [toMat_idM, htAB] at this

private theorem zmod3_pow_eq_one : ∀ x : ZMod 3, x ^ 13 = 1 → x = 1 := by decide

private theorem zmod3_pow11_eq_one : ∀ x : ZMod 3, x ^ 11 = 1 → x = 1 := by decide

section Facts

variable (hM : MatrixFacts)
include hM

theorem det_mB : mB.det = 1 := by
  apply zmod3_pow_eq_one
  rw [← Matrix.det_pow, hM.B_pow, Matrix.det_one]

theorem det_mA : mA.det = 1 := by
  have h : (mA * mB).det = 1 := by
    apply zmod3_pow11_eq_one
    rw [← Matrix.det_pow, hM.AB_pow, Matrix.det_one]
  rwa [Matrix.det_mul, det_mB hM, mul_one] at h

theorem det_mA_ne_zero : mA.det ≠ 0 := by rw [det_mA hM]; exact one_ne_zero

theorem det_mB_ne_zero : mB.det ≠ 0 := by rw [det_mB hM]; exact one_ne_zero

end Facts

@[expose] noncomputable def orb : COrbit := orbitData ()

theorem certificate_parts : matrixChecks = true ∧
    conjOrbitOK 77 matA matA matB matBi orb 3 = true ∧ actionChecks orb 3 = true ∧
    productChecks orb = true := by
  have h := fi22_certificate
  unfold fi22Certificate at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem matrixFacts :
    MatrixFacts := matrixFacts_of certificate_parts.1

noncomputable abbrev gA : GL (Fin 77) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mA (det_mA_ne_zero matrixFacts)

noncomputable abbrev gB : GL (Fin 77) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mB (det_mB_ne_zero matrixFacts)

noncomputable abbrev J :
    Subgroup (GL (Fin 77) (ZMod 3)) := Subgroup.closure {gA, gB}

@[expose] noncomputable def a :
    J := ⟨gA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def b :
    J := ⟨gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem a_val : ((a : GL (Fin 77) (ZMod 3)) : Matrix (Fin 77) (Fin 77) (ZMod 3)) = mA := rfl

theorem b_val : ((b : GL (Fin 77) (ZMod 3)) : Matrix (Fin 77) (Fin 77) (ZMod 3)) = mB := rfl

theorem closure_ab : Subgroup.closure ({a, b} : Set J) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    ({gA, gB} : Set (GL (Fin 77) (ZMod 3)))
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl) <;> simp [a, b]
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

noncomputable def fi22EquivJ : Blueprint.NativeSporadic.Fi22 ≃* J :=
  Blueprint.NativeSporadic.matrixSeedEquiv 3 77 (by norm_num) mA mB (det_mA_ne_zero matrixFacts)
    (det_mB_ne_zero matrixFacts)

theorem det_eq_one (g : J) :
    ((g : GL (Fin 77) (ZMod 3)) : Matrix (Fin 77) (Fin 77) (ZMod 3)).det = 1 := by
  obtain ⟨g, hg⟩ := g
  show (g : Matrix (Fin 77) (Fin 77) (ZMod 3)).det = 1
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact det_mA matrixFacts
    · exact det_mB matrixFacts
  | one => simp
  | mul x y _ _ hx hy => rw [Units.val_mul, Matrix.det_mul, hx, hy, mul_one]
  | inv x _ hx =>
    have h1 := congrArg Matrix.det (Units.mul_inv x)
    rw [Matrix.det_mul, hx, one_mul, Matrix.det_one] at h1
    exact h1

theorem a_inv : a⁻¹ = a := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  apply Units.ext
  show mA * mA = 1
  exact matrixFacts.A_sq

theorem b_inv_val :
    (((b⁻¹ : J) : GL (Fin 77) (ZMod 3)) : Matrix (Fin 77) (Fin 77) (ZMod 3)) = toMat 77 matBi := by
  have h1 : (((b⁻¹ : J) : GL (Fin 77) (ZMod 3)) : Matrix (Fin 77) (Fin 77) (ZMod 3)) * mB = 1 := by
    have := congrArg (fun g : J => ((g : GL (Fin 77) (ZMod 3)) : Matrix (Fin 77) (Fin 77) (ZMod 3)))
      (inv_mul_cancel b)
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] at this
    rwa [b_val] at this
  calc (((b⁻¹ : J) : GL (Fin 77) (ZMod 3)) : Matrix (Fin 77) (Fin 77) (ZMod 3))
      = (((b⁻¹ : J) : GL (Fin 77) (ZMod 3)) : Matrix (Fin 77) (Fin 77) (ZMod 3)) *
          (mB * toMat 77 matBi) := by rw [matrixFacts.B_inv, mul_one]
    _ = ((((b⁻¹ : J) : GL (Fin 77) (ZMod 3)) : Matrix (Fin 77) (Fin 77) (ZMod 3)) * mB) *
          toMat 77 matBi := by rw [mul_assoc]
    _ = toMat 77 matBi := by rw [h1, one_mul]

end CFSG.Sporadic.Fi22
