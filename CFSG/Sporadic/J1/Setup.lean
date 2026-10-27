module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.J1ModelTransport
public import CFSG.Certificates.SchreierStabilizerGenerators
public import CFSG.Sporadic.J1.VecSpec
public import Certificates.Data.CFSGNative.J1.Certificate

public section

namespace CFSG.Sporadic.J1

open CFSG.Blueprint CFSG.ProperTwoGeneratedCore Matrix

noncomputable abbrev J : Subgroup (GL (Fin 7) (ZMod 11)) :=
  Subgroup.closure {j1_first_unit, j1_second_unit}

@[expose] noncomputable def a : J := ⟨j1_first_unit, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def b : J :=
  ⟨j1_second_unit, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

noncomputable abbrev mat (g : J) : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  ((g : GL (Fin 7) (ZMod 11)) : Matrix (Fin 7) (Fin 7) (ZMod 11))

theorem mat_a : mat a = j1_first_matrix := rfl

theorem mat_b : mat b = j1_second_matrix := rfl

theorem mat_mul (g h : J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : J) = 1 := rfl

theorem mat_pow (g : J) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  simp [mat, Units.val_pow_eq_pow_val]

theorem mat_injective : Function.Injective mat := fun _ _ e => Subtype.ext (Units.ext e)

theorem closure_ab : Subgroup.closure ({a, b} : Set J) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    ({j1_first_unit, j1_second_unit} : Set (GL (Fin 7) (ZMod 11)))
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl) <;> simp [a, b]
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

noncomputable def nativeEquiv : NativeSporadic.J1 ≃* J := by
  change (NativeSporadic.seedMonoid 11 7 3 NativeSporadic.J1Seed1 NativeSporadic.J1Seed2)ˣ ≃* _
  rw [j1_seed_monoid_eq]
  exact NativeSporadic.unitSeedEquiv j1_first_unit j1_second_unit

theorem first_ne_one : j1_first_matrix ≠ 1 := by decide +kernel

theorem second_ne_one : j1_second_matrix ≠ 1 := by decide +kernel

theorem prod_pow_seven : (j1_first_matrix * j1_second_matrix) ^ 7 = 1 := by decide +kernel

theorem prod_ne_one : j1_first_matrix * j1_second_matrix ≠ 1 := by decide +kernel

theorem toM_mA : toM 11 7 Native.mA = j1_first_matrix := by decide +kernel

theorem toM_mB : toM 11 7 Native.mB = j1_second_matrix := by decide +kernel

theorem wfM_mA : Native.wfM 7 Native.mA = true := by decide

theorem wfM_mB : Native.wfM 7 Native.mB = true := by decide

private theorem zmod11_pow3 : ∀ x : ZMod 11, x ^ 3 = 1 → x = 1 := by decide

private theorem zmod11_pow7 : ∀ x : ZMod 11, x ^ 7 = 1 → x = 1 := by decide

theorem det_second : j1_second_matrix.det = 1 := by
  apply zmod11_pow3
  rw [← Matrix.det_pow, j1_second_pow_three, Matrix.det_one]

theorem det_first : j1_first_matrix.det = 1 := by
  have h : (j1_first_matrix * j1_second_matrix).det = 1 := by
    apply zmod11_pow7
    rw [← Matrix.det_pow, prod_pow_seven, Matrix.det_one]
  rwa [Matrix.det_mul, det_second, mul_one] at h

theorem det_eq_one (g : J) : (mat g).det = 1 := by
  obtain ⟨g, hg⟩ := g
  show (g : Matrix (Fin 7) (Fin 7) (ZMod 11)).det = 1
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact det_first
    · exact det_second
  | one => simp
  | mul x y _ _ hx hy => rw [Units.val_mul, Matrix.det_mul, hx, hy, mul_one]
  | inv x _ hx =>
    have h1 := congrArg Matrix.det (Units.mul_inv x)
    rw [Matrix.det_mul, hx, one_mul, Matrix.det_one] at h1
    exact h1

theorem eq_one_of_smul_one {g : J} {μ : ZMod 11} (h : mat g = μ • 1) : g = 1 := by
  have hdet := det_eq_one g
  rw [h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  apply mat_injective
  rw [h, zmod11_pow7 μ hdet, one_smul, mat_one]

theorem a_sq : a ^ 2 = 1 := by
  apply mat_injective
  rw [mat_pow, mat_one, mat_a, j1_first_pow_two]

theorem b_cube : b ^ 3 = 1 := by
  apply mat_injective
  rw [mat_pow, mat_one, mat_b, j1_second_pow_three]

theorem ab_pow : (a * b) ^ 7 = 1 := by
  apply mat_injective
  rw [mat_pow, mat_one, mat_mul, mat_a, mat_b, prod_pow_seven]

theorem a_ne_one : a ≠ 1 := fun h => first_ne_one (by rw [← mat_a, h, mat_one])

theorem b_ne_one : b ≠ 1 := fun h => second_ne_one (by rw [← mat_b, h, mat_one])

theorem ab_ne_one : a * b ≠ 1 := fun h =>
  prod_ne_one (by rw [← mat_a, ← mat_b, ← mat_mul, h, mat_one])

theorem orderOf_a : orderOf a = 2 := orderOf_eq_prime a_sq a_ne_one

theorem orderOf_b : orderOf b = 3 := orderOf_eq_prime b_cube b_ne_one

theorem orderOf_ab : orderOf (a * b) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime ab_pow ab_ne_one

@[ext] structure Cong where
  val : Matrix (Fin 7) (Fin 7) (ZMod 11)

noncomputable instance : MulAction J Cong where
  smul g X := ⟨mat g * X.val * (mat g)ᵀ⟩
  one_smul X := by
    ext1
    show mat 1 * X.val * (mat 1)ᵀ = X.val
    rw [mat_one, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
  mul_smul g h X := by
    ext1
    show mat (g * h) * X.val * (mat (g * h))ᵀ = mat g * (mat h * X.val * (mat h)ᵀ) * (mat g)ᵀ
    rw [mat_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

theorem smul_val (g : J) (X : Cong) : (g • X).val = mat g * X.val * (mat g)ᵀ := rfl

theorem smul_vecMulVec (g : J) (v : Fin 7 → ZMod 11) :
    g • (⟨vecMulVec v v⟩ : Cong) = ⟨vecMulVec (mat g *ᵥ v) (mat g *ᵥ v)⟩ := by
  ext1
  rw [smul_val, mul_vecMulVec, vecMulVec_mul, vecMul_transpose]

end CFSG.Sporadic.J1
