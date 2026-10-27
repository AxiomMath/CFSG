module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockRestrict
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneUnitaryModel
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutSimilitude
public import CFSG.RankThree.PartOne.S11d.PerfectCentral
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLargeTorusUnitary

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType SUTB CFSG.LinearGroups


public section

namespace CFSG.StandardType.ResJUnitaryActor

variable {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
variable (h : UnitaryFieldData 2 f K)

omit [Finite K] [CharP K 2] in
theorem normOne_cube_bijective (hpq : ¬ 3 ∣ 2 ^ f + 1) :
    Function.Bijective (fun u : (Units.map h.normHom).ker => u ^ 3) := by
  have hcard : Nat.card (Units.map h.normHom).ker = 2 ^ f + 1 :=
    (unitary_field_norm h).2.2.1
  have hcop : Nat.Coprime (Nat.card (Units.map h.normHom).ker) 3 := by
    rw [hcard]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hpq).symm
  exact (powCoprime hcop).bijective

noncomputable def normOneCubeRoot (hpq : ¬ 3 ∣ 2 ^ f + 1)
    (u : (Units.map h.normHom).ker) : (Units.map h.normHom).ker :=
  (normOne_cube_bijective h hpq).surjective u |>.choose

omit [Finite K] [CharP K 2] in
theorem normOneCubeRoot_pow_three (hpq : ¬ 3 ∣ 2 ^ f + 1)
    (u : (Units.map h.normHom).ker) : normOneCubeRoot h hpq u ^ 3 = u :=
  (normOne_cube_bijective h hpq).surjective u |>.choose_spec

omit [Finite K] [CharP K 2] in
theorem norm_one_of_mem_normOne (r : (Units.map h.normHom).ker) :
    h.norm (((r : Kˣ) : K)) = 1 := by
  have h1 : (Units.map h.normHom) (r : Kˣ) = 1 := MonoidHom.mem_ker.mp r.2
  have h2 := congrArg (fun u : h.fixedFieldˣ => ((u : h.fixedField) : K)) h1
  simpa [Units.coe_map, UnitaryFieldData.coe_normHom] using h2

noncomputable def conjSU (Y : GL (Fin n) K)
    (hY : ∀ x y, stdHermForm h n ((Y : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((Y : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y)
    (g : ↥(unitarySU 2 f K n)) : ↥(unitarySU 2 f K n) := by
  classical
  let M : Matrix (Fin n) (Fin n) K := Y * (g : GL (Fin n) K) * Y⁻¹
  have hgdet : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
    ((mem_unitarySU_iff h).mp g.2).1
  have hdet : M.det = 1 := by
    dsimp [M]
    rw [Matrix.det_mul, Matrix.det_mul, hgdet, mul_one]
    have hinv : ((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
        ((Y : Matrix (Fin n) (Fin n) K).det)⁻¹ := by
      simp
    rw [hinv]
    have hYdet0 : (Y : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
      simpa using (Matrix.GeneralLinearGroup.det Y).ne_zero
    exact mul_inv_cancel₀ hYdet0
  have hYgram : ((Y : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      (Y : Matrix (Fin n) (Fin n) K) = 1 := by
    simpa using SUTB.map_bar_transpose_mul_of_isometry h hY
  have hggram : (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    simpa using SUTB.map_bar_transpose_mul_of_isometry h
      ((mem_unitarySU_iff_isometry h).mp g.2).2
  have hgram := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.isometry_conj_of_unitary
    (h := h) (Q := Y) (G := (1 : Matrix (Fin n) (Fin n) K)) (Y := (g : GL (Fin n) K))
    (by simpa using hYgram) hggram
  have hstd : ∀ x y, stdHermForm h n (M *ᵥ x) (M *ᵥ y) = stdHermForm h n x y := by
    intro x y
    rw [stdHermForm_eq_gramForm]
    exact (gramForm_isometry_iff h 1 M).mpr (by simpa [M] using hgram) x y
  let A : GL (Fin n) K := Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero)
  refine ⟨A, (mem_unitarySU_iff_isometry h).mpr ⟨?_, ?_⟩⟩
  · simpa [A] using hdet
  · simpa [A] using hstd

omit [Finite K] [CharP K 2] in
@[simp] theorem conjSU_coe_GL (Y : GL (Fin n) K)
    (hY : ∀ x y, stdHermForm h n ((Y : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((Y : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y)
    (g : ↥(unitarySU 2 f K n)) :
    (conjSU h Y hY g : GL (Fin n) K) =
      Y * (g : GL (Fin n) K) * Y⁻¹ := by
  apply Units.ext
  simp [conjSU]

omit [Finite K] [CharP K 2] in
@[simp] theorem conjSU_coe (Y : GL (Fin n) K)
    (hY : ∀ x y, stdHermForm h n ((Y : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((Y : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y)
    (g : ↥(unitarySU 2 f K n)) :
    ((conjSU h Y hY g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (Y : Matrix (Fin n) (Fin n) K) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (Y⁻¹ : GL (Fin n) K) := by
  simp [conjSU]


omit [Finite K] [CharP K 2] in
theorem isometry_mul {A B : GL (Fin n) K}
    (hA : ∀ x y, stdHermForm h n ((A : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((A : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y)
    (hB : ∀ x y, stdHermForm h n ((B : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((B : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y) :
    ∀ x y, stdHermForm h n (((A * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x)
      (((A * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y := by
  intro x y
  change stdHermForm h n (((A : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) *ᵥ x)
    (((A : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) *ᵥ y) =
      stdHermForm h n x y
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact (hA _ _).trans (hB x y)

omit [Finite K] [CharP K 2] in
theorem isometry_inv {Y : GL (Fin n) K}
    (hY : ∀ x y, stdHermForm h n ((Y : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((Y : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y) :
    ∀ x y, stdHermForm h n (((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x)
      (((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y := by
  intro x y
  have h1 : ∀ v : Fin n → K,
      (Y : Matrix (Fin n) (Fin n) K) *ᵥ
        (((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  rw [← hY (((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x)
    (((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y), h1, h1]

omit [Finite K] [CharP K 2] in
theorem conjSU_mul (Y : GL (Fin n) K)
    (hY : ∀ x y, stdHermForm h n ((Y : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((Y : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y)
    (g h' : ↥(unitarySU 2 f K n)) :
    conjSU h Y hY (g * h') = conjSU h Y hY g * conjSU h Y hY h' := by
  apply Subtype.ext
  simp only [conjSU_coe_GL, Subgroup.coe_mul]
  group

omit [Finite K] [CharP K 2] in
@[simp] theorem conjSU_one (Y : GL (Fin n) K)
    (hY : ∀ x y, stdHermForm h n ((Y : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((Y : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y) :
    conjSU h Y hY (1 : ↥(unitarySU 2 f K n)) = 1 := by
  apply Subtype.ext
  rw [conjSU_coe_GL]
  simp

noncomputable def conjHomSU (Y : GL (Fin n) K)
    (hY : ∀ x y, stdHermForm h n ((Y : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((Y : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y) :
    ↥(unitarySU 2 f K n) →* ↥(unitarySU 2 f K n) where
  toFun := conjSU h Y hY
  map_one' := conjSU_one h Y hY
  map_mul' := conjSU_mul h Y hY

omit [Finite K] [CharP K 2] in
theorem isometry_pow_three (Y : GL (Fin n) K)
    (hY : ∀ x y, stdHermForm h n ((Y : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((Y : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y) :
    ∀ x y, stdHermForm h n (((Y : Matrix (Fin n) (Fin n) K) ^ 3) *ᵥ x)
      (((Y : Matrix (Fin n) (Fin n) K) ^ 3) *ᵥ y) = stdHermForm h n x y := by
  classical
  have hYgram : ((Y : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      (Y : Matrix (Fin n) (Fin n) K) = 1 := by
    simpa using SUTB.map_bar_transpose_mul_of_isometry h hY
  have hA : ((Y : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ =
      ((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    calc ((Y : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ
        = ((Y : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * 1 := by rw [mul_one]
      _ = ((Y : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
          ((Y : Matrix (Fin n) (Fin n) K) *
            ((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      _ = (((Y : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
            (Y : Matrix (Fin n) (Fin n) K)) *
            ((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [mul_assoc]
      _ = 1 * ((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hYgram]
      _ = ((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := one_mul _
  have hBA : (Y : Matrix (Fin n) (Fin n) K) *
      ((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcomm : Commute ((Y : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ
      (Y : Matrix (Fin n) (Fin n) K) := by
    show ((Y : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      (Y : Matrix (Fin n) (Fin n) K) =
      (Y : Matrix (Fin n) (Fin n) K) *
        ((Y : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ
    rw [hYgram, hA, hBA]
  have hY3gram : (((Y : Matrix (Fin n) (Fin n) K) ^ 3).map h.bar)ᵀ *
      ((Y : Matrix (Fin n) (Fin n) K) ^ 3) = 1 := by
    have hmap : (((Y : Matrix (Fin n) (Fin n) K) ^ 3).map h.bar) =
        ((Y : Matrix (Fin n) (Fin n) K).map h.bar) ^ 3 :=
      Matrix.map_pow (Y : Matrix (Fin n) (Fin n) K) h.bar 3
    rw [hmap, Matrix.transpose_pow, ← hcomm.mul_pow, hYgram, one_pow]
  intro x y
  rw [stdHermForm_eq_gramForm]
  exact (gramForm_isometry_iff h 1 ((Y : Matrix (Fin n) (Fin n) K) ^ 3)).mpr
    (by simpa using hY3gram) x y

omit [Finite K] [CharP K 2] in
theorem norm_one_of_scalar_cube_of_isometry (Y : GL (Fin n) K)
    (hY : ∀ x y, stdHermForm h n ((Y : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((Y : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y)
    (hn : 1 ≤ n) {c : K} (hc : ((Y : Matrix (Fin n) (Fin n) K) ^ 3) = c • 1) :
    h.norm c = 1 := by
  classical
  have hY3iso := isometry_pow_three h Y hY
  have hunit := SUTB.map_bar_transpose_mul_of_isometry h hY3iso
  rw [hc, Matrix.smul_one_eq_diagonal] at hunit
  rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal] at hunit
  have hdiag : (fun _ : Fin n => h.bar c * c) = (fun _ : Fin n => (1 : K)) :=
    Matrix.diagonal_injective hunit
  have hi := congrFun hdiag ⟨0, hn⟩
  simpa [UnitaryFieldData.norm, mul_comm] using hi

omit [Finite K] [CharP K 2] in
theorem norm_one_of_scalar_isometry (Y : GL (Fin n) K)
    (hY : ∀ x y, stdHermForm h n ((Y : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((Y : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y)
    (hn : 1 ≤ n) {c : K} (hc : ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) :
    h.norm c = 1 := by
  classical
  have hunit := SUTB.map_bar_transpose_mul_of_isometry h hY
  rw [hc, Matrix.smul_one_eq_diagonal] at hunit
  rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal] at hunit
  have hdiag : (fun _ : Fin n => h.bar c * c) = (fun _ : Fin n => (1 : K)) :=
    Matrix.diagonal_injective hunit
  have hi := congrFun hdiag ⟨0, hn⟩
  simpa [UnitaryFieldData.norm, mul_comm] using hi

omit [Finite K] [CharP K 2] in
theorem eq_one_of_scalar_cube_of_mem_unitarySU (h : UnitaryFieldData 2 f K)
    {z : ↥(unitarySU 2 f K n)}
    (hpq : ¬ 3 ∣ 2 ^ f + 1) (hn : 1 ≤ n) (hz3 : z ^ 3 = 1)
    (hzscalar : ∃ a : K, (((z : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = a • 1) :
    z = 1 := by
  classical
  obtain ⟨a, ha⟩ := hzscalar
  have hiso : ∀ x y, stdHermForm h n
      (((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x)
      (((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y :=
    ((mem_unitarySU_iff_isometry h).mp z.2).2
  have hnorm : h.norm a = 1 := norm_one_of_scalar_isometry h (z : GL (Fin n) K) hiso hn ha
  have hzGL3 : ((z : GL (Fin n) K)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hz3, Subgroup.coe_one]
  have hzmat3 : ((((z : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hzGL3, Units.val_one]
  have hscalar : (((z : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
      Matrix.scalar (Fin n) a := by
    simpa [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using ha
  have hscalar3 : Matrix.scalar (Fin n) (a ^ 3) = 1 := by
    rw [map_pow, ← hscalar]
    exact hzmat3
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have ha3 : a ^ 3 = 1 := by
    have h : Matrix.scalar (Fin n) (a ^ 3) = Matrix.scalar (Fin n) (1 : K) := by
      simpa using hscalar3
    exact Matrix.scalar_inj.mp h
  have ha_q1 : a ^ (2 ^ f + 1) = 1 := by
    have h := hnorm
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply] at h
    rw [mul_comm] at h
    simpa [pow_succ] using h
  have hcop : Nat.Coprime 3 (2 ^ f + 1) :=
    Nat.prime_three.coprime_iff_not_dvd.mpr hpq
  have ha1 : a = 1 := by
    have h1 : a ^ Nat.gcd 3 (2 ^ f + 1) = 1 :=
      pow_gcd_eq_one.mpr ⟨ha3, ha_q1⟩
    simpa [hcop] using h1
  apply Subtype.ext
  apply Units.ext
  rw [ha, ha1]
  simp

structure NormalizedLift (Y : GL (Fin n) K) where
  U : ↥(unitarySU 2 f K n)
  pow_three : U ^ 3 = 1
  coe_eq : ∃ s : Kˣ, (U : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) s * Y

noncomputable def normalizedLiftOfIsometry (hpq : ¬ 3 ∣ 2 ^ f + 1) (hn : 1 ≤ n)
    (Y : GL (Fin n) K)
    (hYiso : ∀ x y, stdHermForm h n ((Y : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((Y : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y)
    {c : K} (hc : ((Y : Matrix (Fin n) (Fin n) K) ^ 3) = c • 1) :
    NormalizedLift (f := f) (n := n) (K := K) Y := by
  classical
  have hnormc : h.norm c = 1 := norm_one_of_scalar_cube_of_isometry h Y hYiso hn hc
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, UnitaryFieldData.norm, map_zero, zero_mul] at hnormc
    exact zero_ne_one hnormc
  let cU : (Units.map h.normHom).ker := ⟨Units.mk0 c hc0, by
    rw [MonoidHom.mem_ker]
    apply Units.ext
    simp only [Units.coe_map]
    exact Subtype.ext hnormc⟩
  let r : (Units.map h.normHom).ker := normOneCubeRoot h hpq cU
  let U : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) ((r : Kˣ)⁻¹) * Y
  have hr3 : ((r : Kˣ) : K) ^ 3 = c := by
    have h1 := congrArg (fun u : (Units.map h.normHom).ker => ((u : Kˣ) : K))
      (normOneCubeRoot_pow_three h hpq cU)
    simpa [cU, Units.val_pow_eq_pow_val] using h1
  have hU3GL : U ^ 3 = 1 := by
    have hcomm : Commute (GeneralLinearGroup.scalar (Fin n) ((r : Kˣ)⁻¹)) Y :=
      (GeneralLinearGroup.scalar_commute (n := Fin n) ((r : Kˣ)⁻¹) Y)
    change (GeneralLinearGroup.scalar (Fin n) ((r : Kˣ)⁻¹) * Y) ^ 3 = 1
    rw [hcomm.mul_pow]
    have h1 : (GeneralLinearGroup.scalar (Fin n) ((r : Kˣ)⁻¹)) ^ 3 =
        GeneralLinearGroup.scalar (Fin n) (((r : Kˣ)⁻¹) ^ 3) :=
      (map_pow (GeneralLinearGroup.scalar (Fin n)) ((r : Kˣ)⁻¹) 3).symm
    have h2 : ((r : Kˣ)⁻¹) ^ 3 = (Units.mk0 c hc0)⁻¹ := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow, hr3]
      rfl
    have hY3 : Y ^ 3 = GeneralLinearGroup.scalar (Fin n) (Units.mk0 c hc0) := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal]
      exact hc
    rw [h1, h2, hY3, ← map_mul, inv_mul_cancel, map_one]
  have hUmat3 : (((U : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hU3GL, Units.val_one]
  have hUmat : ((U : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.scalar (Fin n) (((r : Kˣ) : K)⁻¹) *
        ((Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    change ((GeneralLinearGroup.scalar (Fin n) ((r : Kˣ)⁻¹) * Y :
      GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = _
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_inv_eq_inv_val]
  have hscalar_mulVec : ∀ v : Fin n → K,
      Matrix.scalar (Fin n) (((r : Kˣ) : K)⁻¹) *ᵥ v = (((r : Kˣ) : K)⁻¹) • v := by
    intro v
    ext i
    simp [Matrix.mulVec, Matrix.scalar, mul_comm]
  have hiso : ∀ x y, stdHermForm h n
      (((U : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x)
      (((U : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y := by
    intro x y
    have hcoenorm : h.norm (((r : Kˣ) : K)⁻¹) = 1 := by
      rw [norm_inv_eq h,
        norm_one_of_mem_normOne h r, inv_one]
    rw [hUmat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hscalar_mulVec, hscalar_mulVec]
    calc stdHermForm h n ((((r : Kˣ) : K)⁻¹) • _) ((((r : Kˣ) : K)⁻¹) • _)
        = h.norm (((r : Kˣ) : K)⁻¹) * stdHermForm h n _ _ :=
          CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.sesq_smul_smul (h := h)
            (B := stdHermForm h n) _ _ _
      _ = stdHermForm h n ((Y : Matrix (Fin n) (Fin n) K) *ᵥ x)
          ((Y : Matrix (Fin n) (Fin n) K) *ᵥ y) := by
          rw [hcoenorm, one_mul]
      _ = stdHermForm h n x y := hYiso x y
  have hdet : (((U : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det = 1 :=
    SUTB.det_eq_one_of_isometry h Nat.prime_three hpq hiso hUmat3
  refine ⟨⟨U, (mem_unitarySU_iff_isometry h).mpr ⟨hdet, hiso⟩⟩, ?_, ⟨(r : Kˣ)⁻¹, rfl⟩⟩
  apply Subtype.ext
  simpa [Subgroup.coe_pow] using hU3GL


omit [Finite K] [CharP K 2] in
theorem exists_scalar_of_commute_unitarySU (h : UnitaryFieldData 2 f K)
    {B : GL (Fin n) K}
    (hB : ∀ g : ↥(unitarySU 2 f K n),
      B * (g : GL (Fin n) K) = (g : GL (Fin n) K) * B) :
    ∃ c : Kˣ, B = GeneralLinearGroup.scalar (Fin n) c := by
  classical
  obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd (n := 2 ^ f + 1) (by
    have := Nat.one_le_two_pow (n := f)
    omega)
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one h.one_le hpq
  have hB' : ∀ g ∈ unitarySU 2 f K n, B * g = g * B := by
    intro g hg
    exact hB ⟨g, hg⟩
  have hN := TableBUE.mem_scalars_of_commute (h := h) (n := f) (d := n) hp hpq hB' 
  rw [CFSG.Assembly.LargeEvenScalars, CFSG.Open.StatedScalars] at hN
  obtain ⟨c, hc⟩ := hN
  exact ⟨c, hc.symm⟩

omit [Finite K] [CharP K 2] in
theorem actor_cube_scalar {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    (hPerf : Group.IsPerfect ↥(unitarySU 2 f K n))
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (φ : ↥(unitarySU 2 f K n) →* ↥J)
    (hker : ∀ g : ↥(unitarySU 2 f K n), φ g = 1 →
      ∃ a : K, (((g : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = a • 1)
    (Y : ↥Bs → GL (Fin n) K)
    (hYiso : ∀ b, ∀ x y, stdHermForm h n ((Y b : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((Y b : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y)
    (hYact : ∀ (b : ↥Bs) (g : ↥(unitarySU 2 f K n)),
      (b : G) * ((φ g : ↥J) : G) * (b : G)⁻¹ =
        ((φ (conjSU h (Y b) (hYiso b) g) : ↥J) : G))
    (hn3 : 3 ≤ n) (b : ↥Bs) :
    ∃ a : K, (((Y b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 = a • 1) ∧
      h.norm a = 1 := by
  classical
  have hb3 : (b : G) ^ 3 = 1 := hBs.2 b b.2
  have htriple : ∀ g : ↥(unitarySU 2 f K n),
      ∃ a : K, ((((Y b : GL (Fin n) K) ^ 3 * (g : GL (Fin n) K) *
        ((Y b : GL (Fin n) K) ^ 3)⁻¹ * (g : GL (Fin n) K)⁻¹ : GL (Fin n) K)) :
        Matrix (Fin n) (Fin n) K) = a • 1 := by
    intro g
    let Z : ↥(unitarySU 2 f K n) :=
      conjSU h (Y b) (hYiso b)
        (conjSU h (Y b) (hYiso b) (conjSU h (Y b) (hYiso b) g))
    have hφZJ : φ Z = φ g := by
      apply Subtype.ext
      have h1 : ((φ Z : ↥J) : G) =
          (b : G) * (b : G) * (b : G) * ((φ g : ↥J) : G) *
            (b : G)⁻¹ * (b : G)⁻¹ * (b : G)⁻¹ := by
        dsimp [Z]
        rw [← hYact b (conjSU h (Y b) (hYiso b)
              (conjSU h (Y b) (hYiso b) g)),
            ← hYact b (conjSU h (Y b) (hYiso b) g),
            ← hYact b g]
        group
      have hb3prod : (b : G) * (b : G) * (b : G) = 1 := by
        simpa [pow_succ, mul_assoc] using hb3
      have hbinv3 : (b : G)⁻¹ * (b : G)⁻¹ * (b : G)⁻¹ = 1 := by
        simpa [pow_succ, mul_assoc, inv_pow, hb3] using congrArg Inv.inv hb3prod
      have hflat : (b : G) * (b : G) * (b : G) * ((φ g : ↥J) : G) *
            (b : G)⁻¹ * (b : G)⁻¹ * (b : G)⁻¹ =
          ((b : G) * (b : G) * (b : G)) * ((φ g : ↥J) : G) *
            ((b : G)⁻¹ * (b : G)⁻¹ * (b : G)⁻¹) := by group
      rw [h1, hflat, hb3prod, hbinv3]
      group
    have hφ1 : φ (Z * g⁻¹) = 1 := by
      rw [map_mul, map_inv, hφZJ, mul_inv_cancel]
    obtain ⟨a, ha⟩ := hker (Z * g⁻¹) hφ1
    refine ⟨a, ?_⟩
    have hZGL : (Z : GL (Fin n) K) =
        (Y b : GL (Fin n) K) ^ 3 * (g : GL (Fin n) K) *
          ((Y b : GL (Fin n) K) ^ 3)⁻¹ := by
      dsimp [Z]
      rw [conjSU_coe_GL, conjSU_coe_GL, conjSU_coe_GL]
      have hY3prod : (Y b : GL (Fin n) K) * (Y b : GL (Fin n) K) *
          (Y b : GL (Fin n) K) = (Y b : GL (Fin n) K) ^ 3 := by
        rw [pow_succ, pow_succ, pow_one]
      rw [← hY3prod, _root_.mul_inv_rev, _root_.mul_inv_rev]
      group
    have hAeq : ((Z * g⁻¹ : ↥(unitarySU 2 f K n)) : GL (Fin n) K) =
        (Y b : GL (Fin n) K) ^ 3 * (g : GL (Fin n) K) *
          ((Y b : GL (Fin n) K) ^ 3)⁻¹ * (g : GL (Fin n) K)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hZGL]
    have hAeqMat := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hAeq
    rw [← hAeqMat]
    exact ha
  have hcenter : ∀ q : GL (Fin n) K, q ∈ unitarySU 2 f K n →
      (Y b : GL (Fin n) K) ^ 3 * q * ((Y b : GL (Fin n) K) ^ 3)⁻¹ * q⁻¹ ∈
        Subgroup.center (GL (Fin n) K) := by
    intro q hq
    obtain ⟨a, ha⟩ := htriple ⟨q, hq⟩
    rw [Subgroup.mem_center_iff]
    intro t
    have ha0 : a ≠ 0 := by
      have : NeZero n := ⟨by omega⟩
      intro h0
      exact Units.ne_zero ((Y b : GL (Fin n) K) ^ 3 * q *
        ((Y b : GL (Fin n) K) ^ 3)⁻¹ * q⁻¹) (by rw [ha, h0, zero_smul])
    have hu : ((Y b : GL (Fin n) K) ^ 3 * q *
        ((Y b : GL (Fin n) K) ^ 3)⁻¹ * q⁻¹) =
        GeneralLinearGroup.scalar (Fin n) (Units.mk0 a ha0) := by
      apply Units.ext
      rw [ha, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.smul_one_eq_diagonal]
      rfl
    rw [hu]
    exact (GeneralLinearGroup.scalar_commute (n := Fin n) (Units.mk0 a ha0) t).symm
  have hcommGL : ∀ g : GL (Fin n) K, g ∈ unitarySU 2 f K n →
      (Y b : GL (Fin n) K) ^ 3 * g = g * (Y b : GL (Fin n) K) ^ 3 := by
    intro g hg
    exact CFSG.RankThree.PartOne.commute_of_commutator_central hPerf
      (Q := unitarySU 2 f K n) hcenter g hg
  have hBmat : ∀ y : GL (Fin n) K, y ∈ unitarySU 2 f K n →
      (((Y b : GL (Fin n) K) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (y : Matrix (Fin n) (Fin n) K) =
      (y : Matrix (Fin n) (Fin n) K) *
        (((Y b : GL (Fin n) K) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro y hy
    exact congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) (hcommGL y hy)
  obtain ⟨c, hc⟩ := exists_scalar_of_commute_unitarySU h
    (B := ((Y b : GL (Fin n) K) ^ 3 : GL (Fin n) K)) (by
      intro g
      exact hcommGL g g.2)
  have hmat : (((Y b : GL (Fin n) K) ^ 3 : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = ((c : K) • 1) := by
    rw [hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]
  have hn : 1 ≤ n := by omega
  refine ⟨(c : K), ?_, ?_⟩
  · simpa [Units.val_pow_eq_pow_val] using hmat
  · exact norm_one_of_scalar_cube_of_isometry h (Y b) (hYiso b) hn
      (by simpa [Units.val_pow_eq_pow_val] using hmat)


omit [Finite K] [CharP K 2] in
theorem actor_commute {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    (hPerf : Group.IsPerfect ↥(unitarySU 2 f K n))
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (φ : ↥(unitarySU 2 f K n) →* ↥J)
    (hker : ∀ g : ↥(unitarySU 2 f K n), φ g = 1 →
      ∃ a : K, (((g : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = a • 1)
    (Y : ↥Bs → GL (Fin n) K)
    (hYiso : ∀ b, ∀ x y, stdHermForm h n ((Y b : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((Y b : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y)
    (hYact : ∀ (b : ↥Bs) (g : ↥(unitarySU 2 f K n)),
      (b : G) * ((φ g : ↥J) : G) * (b : G)⁻¹ =
        ((φ (conjSU h (Y b) (hYiso b) g) : ↥J) : G))
    (hn3 : 3 ≤ n) (hpq : ¬ 3 ∣ 2 ^ f + 1) (b c : ↥Bs) :
    Y b * Y c = Y c * Y b := by
  classical
  have hn : 1 ≤ n := by omega
  set A : GL (Fin n) K := Y b with hAdef
  set B : GL (Fin n) K := Y c with hBdef
  have hAiso : ∀ x y, stdHermForm h n ((A : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((A : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y := hYiso b
  have hBiso : ∀ x y, stdHermForm h n ((B : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((B : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y := hYiso c
  obtain ⟨a, hA3mat, hAnorm⟩ := actor_cube_scalar h hPerf hBs φ hker Y hYiso hYact hn3 b
  obtain ⟨d, hB3mat, hBnorm⟩ := actor_cube_scalar h hPerf hBs φ hker Y hYiso hYact hn3 c
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, UnitaryFieldData.norm, map_zero, zero_mul] at hAnorm
    exact zero_ne_one hAnorm
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, UnitaryFieldData.norm, map_zero, zero_mul] at hBnorm
    exact zero_ne_one hBnorm
  let au : Kˣ := Units.mk0 a ha0
  let du : Kˣ := Units.mk0 d hd0
  have hA3 : A ^ 3 = GeneralLinearGroup.scalar (Fin n) au := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hAdef, hA3mat, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rfl
  have hB3 : B ^ 3 = GeneralLinearGroup.scalar (Fin n) du := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hBdef, hB3mat, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rfl
  let f1 : ↥(unitarySU 2 f K n) →* ↥(unitarySU 2 f K n) :=
    (conjHomSU h A hAiso).comp (conjHomSU h B hBiso)
  let f2 : ↥(unitarySU 2 f K n) →* ↥(unitarySU 2 f K n) :=
    (conjHomSU h B hBiso).comp (conjHomSU h A hAiso)
  have hphi_eq : ∀ g : ↥(unitarySU 2 f K n), φ (f1 g) = φ (f2 g) := by
    intro g
    apply Subtype.ext
    have hbc : (b : G) * (c : G) = (c : G) * (b : G) :=
      congrArg Subtype.val (hBs.1.is_comm.comm b c)
    have h1 : ((φ (f1 g) : ↥J) : G) =
        (b : G) * ((φ (conjSU h B hBiso g) : ↥J) : G) * (b : G)⁻¹ := by
      change ((φ (conjSU h A hAiso (conjSU h B hBiso g)) : ↥J) : G) = _
      exact (hYact b (conjSU h B hBiso g)).symm
    have h2 : ((φ (f2 g) : ↥J) : G) =
        (c : G) * ((φ (conjSU h A hAiso g) : ↥J) : G) * (c : G)⁻¹ := by
      change ((φ (conjSU h B hBiso (conjSU h A hAiso g)) : ↥J) : G) = _
      exact (hYact c (conjSU h A hAiso g)).symm
    calc ((φ (f1 g) : ↥J) : G)
        = (b : G) * ((φ (conjSU h B hBiso g) : ↥J) : G) * (b : G)⁻¹ := h1
      _ = (b : G) * ((c : G) * ((φ g : ↥J) : G) * (c : G)⁻¹) * (b : G)⁻¹ := by
          rw [hYact c g]
      _ = (c : G) * ((b : G) * ((φ g : ↥J) : G) * (b : G)⁻¹) * (c : G)⁻¹ := by
          calc (b : G) * ((c : G) * ((φ g : ↥J) : G) * (c : G)⁻¹) * (b : G)⁻¹
              = ((b : G) * (c : G)) * ((φ g : ↥J) : G) * ((b : G) * (c : G))⁻¹ := by group
            _ = ((c : G) * (b : G)) * ((φ g : ↥J) : G) * ((c : G) * (b : G))⁻¹ := by
                rw [hbc]
            _ = (c : G) * ((b : G) * ((φ g : ↥J) : G) * (b : G)⁻¹) * (c : G)⁻¹ := by group
      _ = (c : G) * ((φ (conjSU h A hAiso g) : ↥J) : G) * (c : G)⁻¹ := by
          rw [hYact b g]
      _ = ((φ (f2 g) : ↥J) : G) := h2.symm

  have hcenter : ∀ g : ↥(unitarySU 2 f K n),
      f1 g * (f2 g)⁻¹ ∈ Subgroup.center ↥(unitarySU 2 f K n) := by
    intro g
    let z : ↥(unitarySU 2 f K n) := f1 g * (f2 g)⁻¹
    have h1 : φ z = 1 := by
      dsimp [z]
      rw [map_mul, map_inv, hphi_eq g, mul_inv_cancel]
    obtain ⟨t, ht⟩ := hker z h1
    have ht0 : t ≠ 0 := by
      have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      have hdetz : ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
        simpa using Matrix.GeneralLinearGroup.det_ne_zero (z : GL (Fin n) K)
      intro h0
      apply hdetz
      rw [ht, h0, zero_smul]
      simp
    have hu : (z : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) (Units.mk0 t ht0) := by
      apply Units.ext
      rw [ht, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.smul_one_eq_diagonal]
      rfl
    rw [Subgroup.mem_center_iff]
    intro u
    apply Subtype.ext
    change (u : GL (Fin n) K) * (z : GL (Fin n) K) =
      (z : GL (Fin n) K) * (u : GL (Fin n) K)
    rw [hu]
    exact (GeneralLinearGroup.scalar_commute (n := Fin n) (Units.mk0 t ht0) u).symm

  have hfeq : f1 = f2 := CFSG.RankThree.PartOne.hom_eq_of_div_central hPerf f1 f2 hcenter
  let P : GL (Fin n) K := A * B
  let Q : GL (Fin n) K := B * A
  let D : GL (Fin n) K := Q⁻¹ * P
  have hDcomm : ∀ g : ↥(unitarySU 2 f K n), D * (g : GL (Fin n) K) =
      (g : GL (Fin n) K) * D := by
    intro g
    have hfg : (f1 g : GL (Fin n) K) = (f2 g : GL (Fin n) K) :=
      congrArg (fun f : ↥(unitarySU 2 f K n) →* ↥(unitarySU 2 f K n) =>
        (f g : GL (Fin n) K)) hfeq
    have hf1 : (f1 g : GL (Fin n) K) = P * (g : GL (Fin n) K) * P⁻¹ := by
      change (conjSU h A hAiso (conjSU h B hBiso g) : GL (Fin n) K) = _
      rw [conjSU_coe_GL, conjSU_coe_GL]
      simp [P]
      group
    have hf2 : (f2 g : GL (Fin n) K) = Q * (g : GL (Fin n) K) * Q⁻¹ := by
      change (conjSU h B hBiso (conjSU h A hAiso g) : GL (Fin n) K) = _
      rw [conjSU_coe_GL, conjSU_coe_GL]
      simp [Q]
      group
    rw [hf1, hf2] at hfg
    calc D * (g : GL (Fin n) K) = Q⁻¹ * (P * (g : GL (Fin n) K) * P⁻¹) * P := by
          simp [D]; group
      _ = Q⁻¹ * (Q * (g : GL (Fin n) K) * Q⁻¹) * P := by rw [hfg]
      _ = (g : GL (Fin n) K) * D := by
          simp [D]; group
  obtain ⟨lam, hDlam⟩ := exists_scalar_of_commute_unitarySU h (B := D) hDcomm
  have hPiso : ∀ x y, stdHermForm h n ((P : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((P : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y := by
    simpa [P] using isometry_mul h hAiso hBiso
  have hQiso : ∀ x y, stdHermForm h n ((Q : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((Q : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y := by
    simpa [Q] using isometry_mul h hBiso hAiso
  have hQinvIso := isometry_inv h hQiso
  have hDiso : ∀ x y, stdHermForm h n ((D : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((D : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y := by
    simpa [D] using isometry_mul h hQinvIso hPiso
  have hDmat : ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (lam : K) • 1 := by
    rw [hDlam, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have hlam_norm : h.norm (lam : K) = 1 :=
    norm_one_of_scalar_isometry h D hDiso hn hDmat
  have hlam3 : lam ^ 3 = 1 := by
    let C : GL (Fin n) K := B⁻¹ * A * B
    have hD' : D = A⁻¹ * C := by
      simp [D, C, P, Q]; group
    have hCeq : C = A * GeneralLinearGroup.scalar (Fin n) lam := by
      calc C = A * (A⁻¹ * C) := by group
        _ = A * D := by rw [hD']
        _ = A * GeneralLinearGroup.scalar (Fin n) lam := by rw [hDlam]
    have hC3 : C ^ 3 = A ^ 3 := by
      calc C ^ 3 = B⁻¹ * A ^ 3 * B := by
            simpa [inv_inv] using conj_pow (a := B⁻¹) (b := A) (i := 3)
        _ = A ^ 3 := by
            rw [hA3, ← GeneralLinearGroup.scalar_commute (n := Fin n) au B⁻¹]
            group
    have hC3scalar : C ^ 3 = GeneralLinearGroup.scalar (Fin n) (au * lam ^ 3) := by
      calc C ^ 3 = (A * GeneralLinearGroup.scalar (Fin n) lam) ^ 3 := by rw [hCeq]
        _ = A ^ 3 * (GeneralLinearGroup.scalar (Fin n) lam) ^ 3 := by
            have hcomm : Commute A (GeneralLinearGroup.scalar (Fin n) lam) :=
              (GeneralLinearGroup.scalar_commute (n := Fin n) lam A).symm
            rw [Commute.mul_pow hcomm]
        _ = GeneralLinearGroup.scalar (Fin n) au *
              GeneralLinearGroup.scalar (Fin n) (lam ^ 3) := by
            rw [hA3, map_pow]
        _ = GeneralLinearGroup.scalar (Fin n) (au * lam ^ 3) := by rw [map_mul]
    have hC3A : C ^ 3 = GeneralLinearGroup.scalar (Fin n) au := hC3.trans hA3
    have hval : ((au * lam ^ 3 : Kˣ) : K) = (au : K) := by
      have hscaleq : GeneralLinearGroup.scalar (Fin n) (au * lam ^ 3) =
          GeneralLinearGroup.scalar (Fin n) au := hC3scalar.symm.trans hC3A
      have hmatval : Matrix.scalar (Fin n) ((au * lam ^ 3 : Kˣ) : K) =
          Matrix.scalar (Fin n) (au : K) := by
        rw [← GeneralLinearGroup.coe_scalar, ← GeneralLinearGroup.coe_scalar]
        exact congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hscaleq
      have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      exact Matrix.scalar_inj.mp hmatval
    apply Units.ext
    have h := mul_left_cancel₀ au.ne_zero (by simpa using hval)
    simpa using h
  have hlam_q1 : (lam : K) ^ (2 ^ f + 1) = 1 := by
    have h := hlam_norm
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply] at h
    rw [mul_comm] at h
    simpa [pow_succ] using h
  have hlam3K : (lam : K) ^ 3 = 1 := by
    simpa using congrArg (fun u : Kˣ => (u : K)) hlam3
  have hcop : Nat.Coprime 3 (2 ^ f + 1) :=
    Nat.prime_three.coprime_iff_not_dvd.mpr hpq
  have hlam1 : lam = 1 := by
    have h1 : (lam : K) ^ Nat.gcd 3 (2 ^ f + 1) = 1 :=
      pow_gcd_eq_one.mpr ⟨hlam3K, hlam_q1⟩
    exact Units.ext (by simpa [hcop] using h1)
  have hD1 : D = 1 := by
    rw [hDlam, hlam1, map_one]
  have hCeqA : B⁻¹ * A * B = A := by
    have hC1 : D = A⁻¹ * (B⁻¹ * A * B) := by
      simp [D, P, Q]; group
    have h := hD1
    rw [hC1] at h
    calc B⁻¹ * A * B = A * (A⁻¹ * (B⁻¹ * A * B)) := by group
      _ = A * 1 := by rw [h]
      _ = A := by simp
  calc A * B = B * (B⁻¹ * A * B) := by group
    _ = B * A := by rw [hCeqA]

omit [Finite K] [CharP K 2] in
theorem exists_normalizedFamily_of_commuting_actors {G : Type} [Group G] [Finite G]
    {Bs J : Subgroup G}
    (hPerf : Group.IsPerfect ↥(unitarySU 2 f K n))
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (φ : ↥(unitarySU 2 f K n) →* ↥J)
    (hker : ∀ g : ↥(unitarySU 2 f K n), φ g = 1 →
      ∃ a : K, (((g : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = a • 1)
    (Y : ↥Bs → GL (Fin n) K)
    (hYiso : ∀ b, ∀ x y, stdHermForm h n ((Y b : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((Y b : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y)
    (hYact : ∀ (b : ↥Bs) (g : ↥(unitarySU 2 f K n)),
      (b : G) * ((φ g : ↥J) : G) * (b : G)⁻¹ =
        ((φ (conjSU h (Y b) (hYiso b) g) : ↥J) : G))
    (hpq : ¬ 3 ∣ 2 ^ f + 1) (hn : 1 ≤ n) (hn3 : 3 ≤ n) :
    ∃ U : ↥Bs → ↥(unitarySU 2 f K n),
      (∀ b, U b ^ 3 = 1) ∧ (∀ b c, U b * U c = U c * U b) ∧
        ∀ (b : ↥Bs) (g : ↥(unitarySU 2 f K n)),
          (b : G) * ((φ g : ↥J) : G) * (b : G)⁻¹ =
            ((φ (U b * g * (U b)⁻¹) : ↥J) : G) := by
  classical
  have hYcomm : ∀ b c : ↥Bs, Y b * Y c = Y c * Y b := fun b c =>
    actor_commute h hPerf hBs φ hker Y hYiso hYact hn3 hpq b c
  have hdata : ∀ b : ↥Bs, ∃ c : K,
      (((Y b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 = c • 1) ∧
        h.norm c = 1 := fun b =>
    actor_cube_scalar h hPerf hBs φ hker Y hYiso hYact hn3 b
  choose c hc hnorm using hdata
  let U : ↥Bs → ↥(unitarySU 2 f K n) := fun b =>
    (normalizedLiftOfIsometry h hpq hn (Y b) (hYiso b) (hc b)).U
  have hpow : ∀ b, U b ^ 3 = 1 := fun b =>
    (normalizedLiftOfIsometry h hpq hn (Y b) (hYiso b) (hc b)).pow_three
  have hcoeeq : ∀ b, ∃ s : Kˣ, (U b : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) s * Y b := fun b =>
    (normalizedLiftOfIsometry h hpq hn (Y b) (hYiso b) (hc b)).coe_eq
  have hcomm : ∀ b c, U b * U c = U c * U b := by
    intro b c
    obtain ⟨sb, hb⟩ := hcoeeq b
    obtain ⟨sc, hc⟩ := hcoeeq c
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hb, hc]
    calc GeneralLinearGroup.scalar (Fin n) sb * Y b *
          (GeneralLinearGroup.scalar (Fin n) sc * Y c)
        = GeneralLinearGroup.scalar (Fin n) sb * (Y b *
            GeneralLinearGroup.scalar (Fin n) sc) * Y c := by group
      _ = GeneralLinearGroup.scalar (Fin n) sb *
            (GeneralLinearGroup.scalar (Fin n) sc * Y b) * Y c := by
          rw [(GeneralLinearGroup.scalar_commute (n := Fin n) sc (Y b)).symm]
      _ = (GeneralLinearGroup.scalar (Fin n) sb *
            GeneralLinearGroup.scalar (Fin n) sc) * (Y b * Y c) := by group
      _ = (GeneralLinearGroup.scalar (Fin n) sb *
            GeneralLinearGroup.scalar (Fin n) sc) * (Y c * Y b) := by rw [hYcomm b c]
      _ = (GeneralLinearGroup.scalar (Fin n) sc *
            GeneralLinearGroup.scalar (Fin n) sb) * (Y c * Y b) := by
          rw [GeneralLinearGroup.scalar_commute (n := Fin n) sb
            (GeneralLinearGroup.scalar (Fin n) sc)]
      _ = GeneralLinearGroup.scalar (Fin n) sc * Y c *
            (GeneralLinearGroup.scalar (Fin n) sb * Y b) := by
          calc GeneralLinearGroup.scalar (Fin n) sc *
                GeneralLinearGroup.scalar (Fin n) sb * (Y c * Y b)
              = GeneralLinearGroup.scalar (Fin n) sc *
                  (GeneralLinearGroup.scalar (Fin n) sb * Y c) * Y b := by group
            _ = GeneralLinearGroup.scalar (Fin n) sc *
                  (Y c * GeneralLinearGroup.scalar (Fin n) sb) * Y b := by
                rw [GeneralLinearGroup.scalar_commute (n := Fin n) sb (Y c)]
            _ = GeneralLinearGroup.scalar (Fin n) sc * Y c *
                  (GeneralLinearGroup.scalar (Fin n) sb * Y b) := by group
  refine ⟨U, hpow, hcomm, ?_⟩
  intro b g
  have hconj : (U b : GL (Fin n) K) * (g : GL (Fin n) K) * (U b : GL (Fin n) K)⁻¹ =
      (Y b : GL (Fin n) K) * (g : GL (Fin n) K) * (Y b : GL (Fin n) K)⁻¹ := by
    obtain ⟨s, hs⟩ := hcoeeq b
    rw [hs]
    rw [_root_.mul_inv_rev]
    rw [show GeneralLinearGroup.scalar (Fin n) s * Y b =
        Y b * GeneralLinearGroup.scalar (Fin n) s from
      (GeneralLinearGroup.scalar_commute (n := Fin n) s (Y b))]
    rw [show Y b * GeneralLinearGroup.scalar (Fin n) s * (g : GL (Fin n) K) =
        Y b * (GeneralLinearGroup.scalar (Fin n) s * (g : GL (Fin n) K)) by group]
    rw [show GeneralLinearGroup.scalar (Fin n) s * (g : GL (Fin n) K) =
        (g : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) s from
      (GeneralLinearGroup.scalar_commute (n := Fin n) s (g : GL (Fin n) K))]
    rw [show Y b * ((g : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) s) *
          ((Y b)⁻¹ * (GeneralLinearGroup.scalar (Fin n) s)⁻¹) =
        Y b * (g : GL (Fin n) K) *
          (GeneralLinearGroup.scalar (Fin n) s * (Y b)⁻¹) *
            (GeneralLinearGroup.scalar (Fin n) s)⁻¹ by group]
    rw [show GeneralLinearGroup.scalar (Fin n) s * (Y b)⁻¹ =
        (Y b)⁻¹ * GeneralLinearGroup.scalar (Fin n) s from
      (GeneralLinearGroup.scalar_commute (n := Fin n) s ((Y b)⁻¹))]
    group
  rw [hYact b g]
  have hJ : φ (conjSU h (Y b) (hYiso b) g) = φ (U b * g * (U b)⁻¹) := by
    have hElem : conjSU h (Y b) (hYiso b) g = U b * g * (U b)⁻¹ := by
      apply Subtype.ext
      simpa [conjSU_coe_GL, Subgroup.coe_mul, Subgroup.coe_inv] using hconj.symm
    exact congrArg φ hElem
  exact congrArg (fun z : ↥J => (z : G)) hJ


end CFSG.StandardType.ResJUnitaryActor

end
