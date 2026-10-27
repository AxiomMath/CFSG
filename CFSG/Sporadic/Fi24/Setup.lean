
module

public import CFSG.Sporadic.Fi24.SetupBase
import all CFSG.Sporadic.Fi24.SetupBase

public import CFSG.Sporadic.Fi24.Certificate
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Fi24

open CFSG.F3.Native Native Matrix

theorem matrixFacts : MatrixFacts :=
  ⟨core_facts.A_sq, core_facts.B_cube, core_facts.AB_pow, core_facts.A_ne, core_facts.B_ne,
    core_facts.AB_ne, core_facts.A_form, core_facts.B_form, rowsWF_matF_form, matF_size_form⟩

theorem det_mB : mB.det = 1 := by
  apply zmod3_pow3_eq_one
  rw [← Matrix.det_pow, pow_three, matrixFacts.B_cube, Matrix.det_one]

theorem det_mA : mA.det = 1 := by
  apply zmod3_pow29_eq_one
  have h := congrArg Matrix.det matrixFacts.AB_pow
  rw [Matrix.det_pow, Matrix.det_mul, det_mB, mul_one, Matrix.det_one] at h
  exact h

theorem det_mA_ne_zero :
    mA.det ≠ 0 := by rw [det_mA]; exact one_ne_zero

theorem det_mB_ne_zero :
    mB.det ≠ 0 := by rw [det_mB]; exact one_ne_zero

noncomputable abbrev gA : GL (Fin 781) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mA det_mA_ne_zero

noncomputable abbrev gB : GL (Fin 781) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero mB det_mB_ne_zero

noncomputable abbrev J :
    Subgroup (GL (Fin 781) (ZMod 3)) := Subgroup.closure {gA, gB}

@[expose] noncomputable def a :
    J := ⟨gA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def b :
    J := ⟨gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

noncomputable abbrev mat
    (g : J) : Matrix (Fin 781) (Fin 781) (ZMod 3) :=
  ((g : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3))

theorem mat_mul (g h : J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : J) = 1 := rfl

theorem mat_pow (g : J) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  simp [mat, Units.val_pow_eq_pow_val]

theorem mat_injective : Function.Injective mat := by
  intro g h e
  exact Subtype.ext (Units.ext e)

theorem mat_a : mat a = mA := rfl

theorem mat_b : mat b = mB := rfl

theorem mat_inv_mul (g : J) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mat_mul_inv (g : J) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

theorem closure_ab : Subgroup.closure ({a, b} : Set J) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    ({gA, gB} : Set (GL (Fin 781) (ZMod 3)))
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl) <;> simp [a, b]
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

noncomputable def fi24EquivJ :
    Blueprint.NativeSporadic.Fi24prime ≃* J :=
  Blueprint.NativeSporadic.matrixSeedEquiv 3 781 (by norm_num) mA mB det_mA_ne_zero
    det_mB_ne_zero

theorem det_eq_one (g : J) : (mat g).det = 1 := by
  obtain ⟨g, hg⟩ := g
  show (g : Matrix (Fin 781) (Fin 781) (ZMod 3)).det = 1
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact det_mA
    · exact det_mB
  | one => simp
  | mul x y _ _ hx hy => rw [Units.val_mul, Matrix.det_mul, hx, hy, mul_one]
  | inv x _ hx =>
    have h1 := congrArg Matrix.det (Units.mul_inv x)
    rw [Matrix.det_mul, hx, one_mul, Matrix.det_one] at h1
    exact h1

theorem form_inv (g : J) : (mat g)ᵀ * mF * mat g = mF := by
  obtain ⟨g, hg⟩ := g
  show (g : Matrix (Fin 781) (Fin 781) (ZMod 3))ᵀ * mF * g = mF
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact matrixFacts.A_form
    · exact matrixFacts.B_form
  | one => simp
  | mul x y _ _ hx hy =>
    set X : Matrix (Fin 781) (Fin 781) (ZMod 3) := (x : Matrix (Fin 781) (Fin 781) (ZMod 3))
    set Y : Matrix (Fin 781) (Fin 781) (ZMod 3) := (y : Matrix (Fin 781) (Fin 781) (ZMod 3))
    show (X * Y)ᵀ * mF * (X * Y) = mF
    calc (X * Y)ᵀ * mF * (X * Y) = Yᵀ * (Xᵀ * mF * X) * Y := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = mF := by rw [hx, hy]
  | inv x _ hx =>
    set M : Matrix (Fin 781) (Fin 781) (ZMod 3) := (x : Matrix (Fin 781) (Fin 781) (ZMod 3))
    set N : Matrix (Fin 781) (Fin 781) (ZMod 3) :=
      ((x⁻¹ : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3))
    have hMN : M * N = 1 := by
      simp only [M, N]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    show Nᵀ * mF * N = mF
    calc Nᵀ * mF * N = Nᵀ * (Mᵀ * mF * M) * N := by rw [hx]
      _ = (M * N)ᵀ * mF * (M * N) := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = mF := by rw [hMN, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem a_sq : a ^ 2 = 1 := by
  apply mat_injective
  rw [mat_pow, mat_one, mat_a, pow_two]
  exact matrixFacts.A_sq

theorem a_ne_one : a ≠ 1 := by
  intro h
  apply matrixFacts.A_ne
  rw [← mat_a, h, mat_one]

theorem b_cube : b ^ 3 = 1 := by
  apply mat_injective
  rw [mat_pow, mat_one, mat_b, pow_three]
  exact matrixFacts.B_cube

theorem b_ne_one : b ≠ 1 := by
  intro h
  apply matrixFacts.B_ne
  rw [← mat_b, h, mat_one]

theorem ab_pow : (a * b) ^ 29 = 1 := by
  apply mat_injective
  rw [mat_pow, mat_one, mat_mul, mat_a, mat_b]
  exact matrixFacts.AB_pow

theorem ab_ne_one : a * b ≠ 1 := by
  intro h
  apply matrixFacts.AB_ne
  rw [← mat_a, ← mat_b, ← mat_mul, h, mat_one]

theorem orderOf_a : orderOf a = 2 := orderOf_eq_prime a_sq a_ne_one

theorem orderOf_b : orderOf b = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime b_cube b_ne_one

theorem orderOf_ab : orderOf (a * b) = 29 := by
  have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  exact orderOf_eq_prime ab_pow ab_ne_one

theorem a_inv : a⁻¹ = a := by
  rw [inv_eq_iff_mul_eq_one]
  apply mat_injective
  exact matrixFacts.A_sq

end CFSG.Sporadic.Fi24
