module

public import Certificates.Data.SmithB45ExcL33
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.Quasithin.B45Exc

namespace L33

open Matrix

variable {K : Type} [Field K] [CharP K 3]

variable {K : Type} [Field K] [CharP K 3]

namespace M3

@[expose] def toK (K : Type) [Field K] (x : M3) : Matrix (Fin 3) (Fin 3) K :=
  !![(x.a : K), x.b, x.c; x.d, x.e, x.f; x.g, x.h, x.i]

@[expose] def R (x : M3) : Prop :=
  x.a < 3 ∧ x.b < 3 ∧ x.c < 3 ∧ x.d < 3 ∧ x.e < 3 ∧ x.f < 3 ∧ x.g < 3 ∧ x.h < 3 ∧ x.i < 3

end M3

omit [CharP K 3] in
theorem natCast_mod_three [CharP K 3] (n : ℕ) : ((n % 3 : ℕ) : K) = n :=
  (CharP.cast_eq_mod K 3 n).symm

theorem three_eq_zero : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3

theorem toK_mul (x y : M3) : (M3.mul x y).toK K = x.toK K * y.toK K := by
  simp only [M3.toK, M3.mul, Matrix.mul_fin_three, natCast_mod_three, Nat.cast_add, Nat.cast_mul]

omit [CharP K 3] in
theorem toK_tr (x : M3) : (M3.tr x).toK K = (x.toK K)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [CharP K 3] in
theorem toK_one : M3.one.toK K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M3.toK, M3.one]

theorem toK_negOne : M3.negOne.toK K = -1 := by
  have h2 : (2 : K) = -1 := by linear_combination (three_eq_zero (K := K))
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M3.toK, M3.negOne, h2]

theorem toK_pow (x : M3) (n : ℕ) : (M3.pow x n).toK K = x.toK K ^ n := by
  induction n with
  | zero => simp [M3.pow, toK_one]
  | succ n ih => rw [M3.pow, toK_mul, ih, pow_succ]

theorem toK_det (x : M3) : ((M3.det x : ℕ) : K) = (x.toK K).det := by
  rw [Matrix.det_fin_three]
  simp only [M3.toK, M3.det, natCast_mod_three, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const]
  linear_combination ((x.a : K) * x.f * x.h + x.b * x.d * x.i + x.b * x.f * x.g +
    x.c * x.e * x.g) * three_eq_zero (K := K)

theorem R_mul (x y : M3) : (M3.mul x y).R :=
  ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩

theorem R_one : M3.one.R := by
  simp only [M3.R, M3.one]
  omega

theorem R_pow (x : M3) (n : ℕ) : (M3.pow x n).R := by
  cases n with
  | zero => exact R_one
  | succ n => exact R_mul _ _

theorem R_tr {x : M3} (hx : x.R) : (M3.tr x).R := by
  obtain ⟨ha, hb, hc, hd, he, hf, hg, hh, hi⟩ := hx
  exact ⟨ha, hd, hg, hb, he, hh, hc, hf, hi⟩

theorem natCast_inj_of_lt {m n : ℕ} (hm : m < 3) (hn : n < 3) (h : (m : K) = n) : m = n := by
  rw [CharP.natCast_eq_natCast K 3] at h
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] at h

theorem toK_inj {x y : M3} (hx : x.R) (hy : y.R) (h : x.toK K = y.toK K) : x = y := by
  obtain ⟨a, b, c, d, e, f, g, h', i⟩ := x
  obtain ⟨a', b', c', d', e', f', g', h'', i'⟩ := y
  obtain ⟨ha, hb, hc, hd, he, hf, hg, hh, hi⟩ := hx
  obtain ⟨ha', hb', hc', hd', he', hf', hg', hh', hi'⟩ := hy
  have e := fun i j => congrFun (congrFun h i) j
  simp only [M3.toK] at e
  simp only [M3.mk.injEq]
  refine ⟨natCast_inj_of_lt ha ha' (by simpa using e 0 0), natCast_inj_of_lt hb hb'
    (by simpa using e 0 1), natCast_inj_of_lt hc hc' (by simpa using e 0 2),
    natCast_inj_of_lt hd hd' (by simpa using e 1 0), natCast_inj_of_lt he he'
    (by simpa using e 1 1), natCast_inj_of_lt hf hf' (by simpa using e 1 2),
    natCast_inj_of_lt hg hg' (by simpa using e 2 0), natCast_inj_of_lt hh hh'
    (by simpa using e 2 1), natCast_inj_of_lt hi hi' (by simpa using e 2 2)⟩

omit [CharP K 3] in
theorem exists_toK (hrep : ∀ k : K, ∃ n : ℕ, n < 3 ∧ (n : K) = k) (M : Matrix (Fin 3) (Fin 3) K) :
    ∃ x : M3, x.R ∧ x.toK K = M := by
  choose f hf1 hf2 using hrep
  refine ⟨⟨f (M 0 0), f (M 0 1), f (M 0 2), f (M 1 0), f (M 1 1), f (M 1 2), f (M 2 0),
    f (M 2 1), f (M 2 2)⟩, ⟨hf1 _, hf1 _, hf1 _, hf1 _, hf1 _, hf1 _, hf1 _, hf1 _, hf1 _⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M3.toK, hf2]

theorem toK_ne_one {x : M3} (hx : x.R) (h : x ≠ M3.one) : x.toK K ≠ 1 := fun h' =>
  h (toK_inj hx R_one (by rw [h', toK_one]))

theorem isSO_of {B x : M3} (hdet : (x.toK K).det = 1) (hB : B.R)
    (h : x.toK K * B.toK K * (x.toK K)ᵀ = B.toK K) : M3.isSO B x = true := by
  have e1 : M3.det x = 1 := by
    have h1 : ((M3.det x : ℕ) : K) = ((1 : ℕ) : K) := by rw [toK_det, hdet, Nat.cast_one]
    exact natCast_inj_of_lt (K := K) (Nat.mod_lt _ (by norm_num)) (by norm_num) h1
  have e2 : M3.mul x (M3.mul B (M3.tr x)) = B :=
    toK_inj (K := K) (R_mul _ _) hB (by rw [toK_mul, toK_mul, toK_tr, ← Matrix.mul_assoc, h])
  simp [M3.isSO, e1, e2]

theorem of_isSO {B x : M3} (h : M3.isSO B x = true) :
    (x.toK K).det = 1 ∧ x.toK K * B.toK K * (x.toK K)ᵀ = B.toK K := by
  simp only [M3.isSO, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨by rw [← toK_det, h.1, Nat.cast_one], ?_⟩
  have := congrArg (M3.toK K) h.2
  rwa [toK_mul, toK_mul, toK_tr, ← Matrix.mul_assoc] at this

section SL3

open CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem eq_one_of_mem_center {x : SpecialLinearGroup (Fin 3) K}
    (hx : x ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K)) : x = 1 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hx
  rw [Fintype.card_fin] at hr
  have h1 : (r - 1) ^ 3 = 0 := by rw [sub_pow_char, hr, one_pow, sub_self]
  have h2 : r = 1 := sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h1)
  apply Subtype.ext
  rw [← hrx, h2, map_one, Matrix.SpecialLinearGroup.coe_one]

@[expose] noncomputable def sigA (A : GL (Fin 3) K) : MulAut (SpecialLinearGroup (Fin 3) K) :=
  CatalogueBHigherLinearAction.slConjugation 3 K A * CatalogueBGraphForm.slGraphAut 3 K

omit [CharP K 3] in
theorem descendAut_sigA (A : GL (Fin 3) K) :
    descendAut 3 K (sigA A) = conjAut 3 K A * dualAut 3 K := by
  simp only [sigA, map_mul]; rfl

omit [CharP K 3] in
theorem coe_sigA (A : GL (Fin 3) K) (x : SpecialLinearGroup (Fin 3) K) :
    ((sigA A x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) *
        ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  simp only [sigA, MulAut.mul_apply]
  rw [CatalogueBHigherLinearAction.slConjugation_matrix, CatalogueBGraphForm.slGraphAut_matrix]

omit [CharP K 3] in
theorem coe_mul_coe_inv (x : SpecialLinearGroup (Fin 3) K) :
    (x : Matrix (Fin 3) (Fin 3) K) * ((x⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

omit [CharP K 3] in
theorem coe_inv_mul_coe (x : SpecialLinearGroup (Fin 3) K) :
    ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (x : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

omit [CharP K 3] in
theorem coe_inv_eq {x : SpecialLinearGroup (Fin 3) K} {Y : Matrix (Fin 3) (Fin 3) K}
    (h : (x : Matrix (Fin 3) (Fin 3) K) * Y = 1) :
    ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Y := by
  calc ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((x : Matrix (Fin 3) (Fin 3) K) * Y) := by rw [h, Matrix.mul_one]
    _ = Y := by rw [← Matrix.mul_assoc, coe_inv_mul_coe, Matrix.one_mul]

omit [CharP K 3] in
theorem mul_eq_of_form {X Xi M : Matrix (Fin 3) (Fin 3) K} (hXiX : Xi * X = 1)
    (h : X * M * Xᵀ = M) : X * M = M * Xiᵀ := by
  calc X * M = X * M * (Xi * X)ᵀ := by rw [hXiX, Matrix.transpose_one, Matrix.mul_one]
    _ = X * M * Xᵀ * Xiᵀ := by rw [Matrix.transpose_mul, Matrix.mul_assoc (X * M)]
    _ = M * Xiᵀ := by rw [h]

omit [CharP K 3] in
theorem coe_mul_coe_inv_GL (A : GL (Fin 3) K) :
    (A : Matrix (Fin 3) (Fin 3) K) * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

omit [CharP K 3] in
theorem coe_inv_mul_coe_GL (A : GL (Fin 3) K) :
    ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

omit [CharP K 3] in
theorem sigA_eq_self {A : GL (Fin 3) K} {x : SpecialLinearGroup (Fin 3) K}
    (hx : (x : Matrix (Fin 3) (Fin 3) K) * A * (x : Matrix (Fin 3) (Fin 3) K)ᵀ = A) :
    sigA A x = x := by
  apply Subtype.ext
  show ((sigA A x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = x
  rw [coe_sigA, ← mul_eq_of_form (coe_inv_mul_coe x) hx, Matrix.mul_assoc,
    coe_mul_coe_inv_GL, Matrix.mul_one]

omit [CharP K 3] in
theorem conj_sigA_eq_self {A : GL (Fin 3) K} {t x : SpecialLinearGroup (Fin 3) K}
    (hx : (x : Matrix (Fin 3) (Fin 3) K) * ((t : Matrix (Fin 3) (Fin 3) K) * A) *
      (x : Matrix (Fin 3) (Fin 3) K)ᵀ = (t : Matrix (Fin 3) (Fin 3) K) * A) :
    t * sigA A x * t⁻¹ = x := by
  apply Subtype.ext
  show ((t * sigA A x * t⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = x
  have key := mul_eq_of_form (coe_inv_mul_coe x) hx
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sigA]
  calc (t : Matrix (Fin 3) (Fin 3) K) * ((A : Matrix (Fin 3) (Fin 3) K) *
        ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ *
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
        ((t⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = ((t : Matrix (Fin 3) (Fin 3) K) * A *
          ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ) *
          ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((t⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        simp only [Matrix.mul_assoc]
    _ = (x : Matrix (Fin 3) (Fin 3) K) * (t : Matrix (Fin 3) (Fin 3) K) *
          ((A : Matrix (Fin 3) (Fin 3) K) * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
          ((t⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [← key]; simp only [Matrix.mul_assoc]
    _ = x := by
        rw [coe_mul_coe_inv_GL, Matrix.mul_one, Matrix.mul_assoc, coe_mul_coe_inv, Matrix.mul_one]

omit [CharP K 3] in
theorem sigA_eq_inv {A : GL (Fin 3) K} {y : SpecialLinearGroup (Fin 3) K}
    (hy : (y : Matrix (Fin 3) (Fin 3) K) * A = A * (y : Matrix (Fin 3) (Fin 3) K)ᵀ) :
    sigA A y = y⁻¹ := by
  apply Subtype.ext
  show ((sigA A y : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    ((y⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  set Y : Matrix (Fin 3) (Fin 3) K := ↑y
  set Yi : Matrix (Fin 3) (Fin 3) K := ((y⁻¹ : SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K)
  have hYiY : Yi * Y = 1 := coe_inv_mul_coe y
  have key : (A : Matrix (Fin 3) (Fin 3) K) * Yiᵀ = Yi * A := by
    calc (A : Matrix (Fin 3) (Fin 3) K) * Yiᵀ = Yi * (Y * A) * Yiᵀ := by
          rw [← Matrix.mul_assoc Yi Y, hYiY, Matrix.one_mul]
      _ = Yi * A * (Yi * Y)ᵀ := by
          rw [hy, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = Yi * A := by rw [hYiY, Matrix.transpose_one, Matrix.mul_one]
  rw [coe_sigA, key, Matrix.mul_assoc, coe_mul_coe_inv_GL, Matrix.mul_one]

omit [CharP K 3] in
theorem form_of_sigA_eq_self {A : GL (Fin 3) K} {t : SpecialLinearGroup (Fin 3) K}
    (h : sigA A t = t) :
    (t : Matrix (Fin 3) (Fin 3) K) * A * (t : Matrix (Fin 3) (Fin 3) K)ᵀ = A := by
  have h1 := congrArg (fun z : SpecialLinearGroup (Fin 3) K => (z : Matrix (Fin 3) (Fin 3) K)) h
  simp only [coe_sigA] at h1
  set T : Matrix (Fin 3) (Fin 3) K := ↑t
  set Ti : Matrix (Fin 3) (Fin 3) K := ((t⁻¹ : SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K)
  calc T * A * Tᵀ = (A * Tiᵀ * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * A * Tᵀ := by
        rw [h1]
    _ = A * Tiᵀ * (((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A) * Tᵀ := by
        simp only [Matrix.mul_assoc]
    _ = A * (T * Ti)ᵀ := by
        rw [coe_inv_mul_coe_GL, Matrix.mul_one, Matrix.mul_assoc, ← Matrix.transpose_mul]
    _ = A := by rw [coe_mul_coe_inv, Matrix.transpose_one, Matrix.mul_one]

end SL3

end L33

end CFSG.Quasithin.B45Exc
