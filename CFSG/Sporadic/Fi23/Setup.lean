
module

public import CFSG.Sporadic.Fi23.SetupBase
import all CFSG.Sporadic.Fi23.SetupBase

public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Certificates.SchreierStabilizerGenerators
public import CFSG.Sporadic.Fi23.Certificate
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Fi23

open CFSG.F3.Native Native Matrix

section Facts

variable (hM : MatrixFacts)
include hM

end Facts

theorem certificate_parts : matrixChecks = true ∧
    conjOrbitOKW 253 matD matA matA matB matBi orb 3 = true ∧ actionChecks orb 3 = true ∧
    productChecks orb = true := by
  have h := fi23_certificate
  unfold fi23Certificate at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem matrixFacts :
    MatrixFacts := matrixFacts_of certificate_parts.1

noncomputable abbrev gA : GL (Fin 253) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mA (det_mA_ne_zero matrixFacts)

noncomputable abbrev gB : GL (Fin 253) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mB (det_mB_ne_zero matrixFacts)

noncomputable abbrev J :
    Subgroup (GL (Fin 253) (ZMod 3)) := Subgroup.closure {gA, gB}

@[expose] noncomputable def a :
    J := ⟨gA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def b :
    J := ⟨gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

noncomputable abbrev mat
    (g : J) : Matrix (Fin 253) (Fin 253) (ZMod 3) :=
  ((g : GL (Fin 253) (ZMod 3)) : Matrix (Fin 253) (Fin 253) (ZMod 3))

theorem mat_mul (g h : J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : J) = 1 := rfl

theorem mat_pow (g : J) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  simp [mat, Units.val_pow_eq_pow_val]

theorem mat_injective : Function.Injective mat := by
  intro g h e
  exact Subtype.ext (Units.ext e)

theorem mat_a : mat a = mA := rfl

theorem mat_b : mat b = mB := rfl

theorem closure_ab : Subgroup.closure ({a, b} : Set J) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    ({gA, gB} : Set (GL (Fin 253) (ZMod 3)))
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl) <;> simp [a, b]
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

noncomputable def fi23EquivJ : Blueprint.NativeSporadic.Fi23 ≃* J :=
  Blueprint.NativeSporadic.matrixSeedEquiv 3 253 (by norm_num) mA mB (det_mA_ne_zero matrixFacts)
    (det_mB_ne_zero matrixFacts)

theorem det_eq_one (g : J) : (mat g).det = 1 := by
  obtain ⟨g, hg⟩ := g
  show (g : Matrix (Fin 253) (Fin 253) (ZMod 3)).det = 1
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
  apply mat_injective
  exact matrixFacts.A_sq

theorem mat_b_inv : mat b⁻¹ = toMatW 253 matBi := by
  rw [toMatW_matBi]
  have h1 : mat b⁻¹ * mB = 1 := by
    rw [← mat_b, ← mat_mul, inv_mul_cancel, mat_one]
  calc mat b⁻¹ = mat b⁻¹ * (mB * (mB * mB)) := by rw [matrixFacts.B_inv, mul_one]
    _ = (mat b⁻¹ * mB) * (mB * mB) := by rw [mul_assoc]
    _ = mB * mB := by rw [h1, one_mul]

@[expose] noncomputable def wordJ
    (w : List ℕ) : J := (w.map fun x => if x = 0 then a else b).prod

theorem mat_wordJ
    (w : List ℕ) : mat (wordJ w) = (w.map genMat).prod := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [wordJ, List.map_cons, List.prod_cons, mat_mul, ← wordJ, ih, List.map_cons,
      List.prod_cons]
    unfold genMat
    split_ifs <;> rfl

@[expose] noncomputable def d : J := wordJ dWord ^ 7

theorem mat_d : mat d = toMatW 253 matD := by
  rw [d, mat_pow, mat_wordJ, matD_facts.2.2]

theorem d_sq : d * d = 1 := by
  apply mat_injective
  rw [mat_mul, mat_d, matD_facts.2.2, mat_one]
  exact matrixFacts.D_sq

theorem d_ne_one : d ≠ 1 := by
  intro h
  apply matrixFacts.D_ne
  rw [← matD_facts.2.2, ← mat_d, h, mat_one]

theorem d_inv : d⁻¹ = d := by
  rw [inv_eq_iff_mul_eq_one]; exact d_sq

end CFSG.Sporadic.Fi23
