module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4EmbDef
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4Tis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (sym2 sym2_transpose tau coe_tau)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  (torusHom coe_torusHom torus statedSp_ext sl2Diag)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular mem_unitriangular)
open Matrix

noncomputable section

variable {F : Type} [Field F]

private def wcgapenC (b c : F) : Matrix (Fin 2) (Fin 2) F := sym2 b c 0

private def wcgapenCinv (b c : F) : Matrix (Fin 2) (Fin 2) F := (c ^ 2)⁻¹ • sym2 0 c b

private lemma wcgapenC_transpose (b c : F) : (wcgapenC b c)ᵀ = wcgapenC b c :=
  sym2_transpose b c 0

private lemma wcgapenCinv_transpose (b c : F) : (wcgapenCinv b c)ᵀ = wcgapenCinv b c := by
  rw [wcgapenCinv, Matrix.transpose_smul, sym2_transpose]

private lemma wcgapenC_01 (b c : F) : wcgapenC b c 0 1 = c := by
  simp [wcgapenC, sym2]

private lemma wcgapenCinv_01 (b c : F) (hc : c ≠ 0) : wcgapenCinv b c 0 1 = c⁻¹ := by
  rw [wcgapenCinv, Matrix.smul_apply,
    show (sym2 0 c b : Matrix (Fin 2) (Fin 2) F) 0 1 = c from by simp [sym2], smul_eq_mul]
  field_simp

private lemma wcgapenCadj_mul (b c : F) [CharP F 2] :
    sym2 b c 0 * sym2 0 c b = c ^ 2 • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sym2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply,
      mul_comm c b, CharTwo.add_self_eq_zero, pow_two]

private lemma wcgapenCadj_mul' (b c : F) [CharP F 2] :
    sym2 0 c b * sym2 b c 0 = c ^ 2 • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sym2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply,
      mul_comm c b, CharTwo.add_self_eq_zero, pow_two]

private lemma wcgapenC_mul_Cinv (b c : F) (hc : c ≠ 0) [CharP F 2] :
    wcgapenC b c * wcgapenCinv b c = 1 := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  rw [wcgapenC, wcgapenCinv, Matrix.mul_smul, wcgapenCadj_mul, smul_smul,
    inv_mul_cancel₀ hc2, one_smul]

private lemma wcgapenCinv_mul_C (b c : F) (hc : c ≠ 0) [CharP F 2] :
    wcgapenCinv b c * wcgapenC b c = 1 := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  rw [wcgapenC, wcgapenCinv, Matrix.smul_mul, wcgapenCadj_mul', smul_smul,
    inv_mul_cancel₀ hc2, one_smul]

private def wcgapenEmbM (b c : F) (M : Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks (M 0 0 • 1) (M 0 1 • wcgapenC b c) (M 1 0 • wcgapenCinv b c) (M 1 1 • 1)

private lemma wcgapen_blocks_mul {C Cinv : Matrix (Fin 2) (Fin 2) F}
    (hmul : C * Cinv = 1) (hmul' : Cinv * C = 1) (a b c d a' b' c' d' : F) :
    fromBlocks (a • 1) (b • C) (c • Cinv) (d • 1) *
        fromBlocks (a' • 1) (b' • C) (c' • Cinv) (d' • 1) =
      fromBlocks ((a * a' + b * c') • 1) ((a * b' + b * d') • C)
        ((c * a' + d * c') • Cinv) ((c * b' + d * d') • 1) := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, hmul, smul_smul]
    rw [← add_smul]
    congr 1
    ring
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
    rw [← add_smul]
    congr 1
    ring
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, smul_smul]
    rw [← add_smul]
    congr 1
    ring
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, hmul', smul_smul]
    rw [← add_smul]
    congr 1
    ring

private lemma wcgapen_blocks_gram {C Cinv : Matrix (Fin 2) (Fin 2) F} [CharP F 2]
    (hCt : Cᵀ = C) (hCit : Cinvᵀ = Cinv) (hmul : C * Cinv = 1) (hmul' : Cinv * C = 1)
    (a b c d : F) (hdet : a * d - b * c = 1) :
    (fromBlocks (a • 1) (b • C) (c • Cinv) (d • 1))ᵀ * fromBlocks 0 1 (-1) 0 *
        fromBlocks (a • 1) (b • C) (c • Cinv) (d • 1) = fromBlocks 0 1 (-1) 0 := by
  have hJ : (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      fromBlocks 0 1 (1 : Matrix (Fin 2) (Fin 2) F) 0 := by
    rw [Matrix.fromBlocks_inj]
    refine ⟨rfl, rfl, ?_, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.neg_apply, Matrix.one_apply, CharTwo.neg_eq]
  rw [hJ]
  have ht : (fromBlocks (a • 1) (b • C) (c • Cinv) (d • 1))ᵀ =
      fromBlocks (a • 1) (c • Cinv) (b • C) (d • 1) := by
    rw [Matrix.fromBlocks_transpose]
    simp only [Matrix.transpose_smul, Matrix.transpose_one, hCt, hCit]
  rw [ht]
  have h1 : fromBlocks (a • 1) (c • Cinv) (b • C) (d • 1) *
        fromBlocks 0 1 (1 : Matrix (Fin 2) (Fin 2) F) 0 =
      fromBlocks (c • Cinv) (a • 1) (d • 1) (b • C) := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Matrix.mul_zero, zero_add, Matrix.mul_one]
    · simp only [Matrix.mul_one, Matrix.mul_zero, add_zero]
    · simp only [Matrix.mul_zero, zero_add, Matrix.mul_one]
    · simp only [Matrix.mul_one, Matrix.mul_zero, add_zero]
  rw [h1, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, smul_smul]
    rw [mul_comm c a, ← add_smul, CharTwo.add_self_eq_zero, zero_smul]
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, hmul']
    rw [← add_smul]
    have hdet' : a * d + b * c = 1 := by rwa [CharTwo.sub_eq_add] at hdet
    rw [show (b * c + d * a) • (1 : Matrix (Fin 2) (Fin 2) F) = 1 from by
      rw [show b * c + d * a = 1 from by linear_combination hdet', one_smul]]
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, hmul]
    rw [← add_smul]
    have hdet' : a * d + b * c = 1 := by rwa [CharTwo.sub_eq_add] at hdet
    rw [show (a * d + c * b) • (1 : Matrix (Fin 2) (Fin 2) F) = 1 from by
      rw [show a * d + c * b = 1 from by linear_combination hdet', one_smul]]
  · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
    rw [mul_comm d b, ← add_smul, CharTwo.add_self_eq_zero, zero_smul]

private lemma wcgapen_det_rel (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 -
        (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
  have h := g.2
  rwa [Matrix.det_fin_two] at h

private lemma wcgapenEmbM_mul (b c : F) (hc : c ≠ 0) [CharP F 2]
    (g h : Matrix.SpecialLinearGroup (Fin 2) F) :
    wcgapenEmbM b c ((g * h : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) =
      wcgapenEmbM b c (g : Matrix (Fin 2) (Fin 2) F) *
        wcgapenEmbM b c (h : Matrix (Fin 2) (Fin 2) F) := by
  have h00 : ((g * h : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (h : Matrix (Fin 2) (Fin 2) F) 0 0 +
        (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (h : Matrix (Fin 2) (Fin 2) F) 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h01 : ((g * h : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (h : Matrix (Fin 2) (Fin 2) F) 0 1 +
        (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (h : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : ((g * h : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 =
      (g : Matrix (Fin 2) (Fin 2) F) 1 0 * (h : Matrix (Fin 2) (Fin 2) F) 0 0 +
        (g : Matrix (Fin 2) (Fin 2) F) 1 1 * (h : Matrix (Fin 2) (Fin 2) F) 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : ((g * h : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
      (g : Matrix (Fin 2) (Fin 2) F) 1 0 * (h : Matrix (Fin 2) (Fin 2) F) 0 1 +
        (g : Matrix (Fin 2) (Fin 2) F) 1 1 * (h : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [wcgapenEmbM, h00, h01, h10, h11]
  rw [wcgapen_blocks_mul (wcgapenC_mul_Cinv b c hc) (wcgapenCinv_mul_C b c hc)]

private lemma wcgapenEmbM_one (b c : F) :
    wcgapenEmbM b c ((1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [wcgapenEmbM]
  have h00 : ((1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    simp
  have h01 : ((1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    simp
  have h10 : ((1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    simp
  have h11 : ((1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    simp
  rw [h00, h01, h10, h11]
  simp [Matrix.fromBlocks_one]

private lemma wcgapenEmbM_gram (b c : F) (hc : c ≠ 0) [CharP F 2]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (wcgapenEmbM b c (g : Matrix (Fin 2) (Fin 2) F))ᵀ * fromBlocks 0 1 (-1) 0 *
        wcgapenEmbM b c (g : Matrix (Fin 2) (Fin 2) F) = fromBlocks 0 1 (-1) 0 := by
  rw [wcgapenEmbM]
  exact wcgapen_blocks_gram (wcgapenC_transpose b c) (wcgapenCinv_transpose b c)
    (wcgapenC_mul_Cinv b c hc) (wcgapenCinv_mul_C b c hc)
    ((g : Matrix (Fin 2) (Fin 2) F) 0 0) ((g : Matrix (Fin 2) (Fin 2) F) 0 1)
    ((g : Matrix (Fin 2) (Fin 2) F) 1 0) ((g : Matrix (Fin 2) (Fin 2) F) 1 1)
    (wcgapen_det_rel g)

private lemma wcgapenEmbM_isUnit_det (b c : F) (hc : c ≠ 0) [CharP F 2]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    IsUnit (wcgapenEmbM b c (g : Matrix (Fin 2) (Fin 2) F)).det :=
  SymplecticGroup.symplectic_det
    ((CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup _).mp
      (wcgapenEmbM_gram b c hc g))

private lemma wcgapenEmbM_mem (b c : F) (hc : c ≠ 0) [CharP F 2]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix.GeneralLinearGroup.mk'' (wcgapenEmbM b c (g : Matrix (Fin 2) (Fin 2) F))
        (wcgapenEmbM_isUnit_det b c hc g) ∈ StatedSp 2 F := by
  rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic,
    TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup]
  simpa using (CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup _).mp
    (wcgapenEmbM_gram b c hc g)

private noncomputable def wcgapenIotaFn (b c : F) (hc : c ≠ 0) [CharP F 2]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) : StatedSp 2 F :=
  ⟨Matrix.GeneralLinearGroup.mk'' (wcgapenEmbM b c (g : Matrix (Fin 2) (Fin 2) F))
      (wcgapenEmbM_isUnit_det b c hc g), wcgapenEmbM_mem b c hc g⟩

@[simp] private theorem wcgapenIotaFn_coe (b c : F) (hc : c ≠ 0) [CharP F 2]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (((wcgapenIotaFn b c hc g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        wcgapenEmbM b c (g : Matrix (Fin 2) (Fin 2) F) := by
  simp [wcgapenIotaFn]

private theorem wcgapenIotaFn_one (b c : F) (hc : c ≠ 0) [CharP F 2] :
    wcgapenIotaFn b c hc (1 : Matrix.SpecialLinearGroup (Fin 2) F) = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_one, Units.val_one, wcgapenIotaFn_coe, wcgapenEmbM_one]

private theorem wcgapenIotaFn_mul (b c : F) (hc : c ≠ 0) [CharP F 2]
    (g h : Matrix.SpecialLinearGroup (Fin 2) F) :
    wcgapenIotaFn b c hc (g * h) = wcgapenIotaFn b c hc g * wcgapenIotaFn b c hc h := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, wcgapenIotaFn_coe, wcgapenEmbM_mul b c hc]

private noncomputable def wcgapenIota (b c : F) (hc : c ≠ 0) [CharP F 2] :
    Matrix.SpecialLinearGroup (Fin 2) F →* StatedSp 2 F where
  toFun := wcgapenIotaFn b c hc
  map_one' := wcgapenIotaFn_one b c hc
  map_mul' := wcgapenIotaFn_mul b c hc

@[simp] private theorem wcgapenIota_apply (b c : F) (hc : c ≠ 0) [CharP F 2]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    wcgapenIota b c hc g = wcgapenIotaFn b c hc g := rfl

@[simp] private theorem wcgapenIota_coe (b c : F) (hc : c ≠ 0) [CharP F 2]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (((wcgapenIota b c hc g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        wcgapenEmbM b c (g : Matrix (Fin 2) (Fin 2) F) := by
  rw [wcgapenIota_apply, wcgapenIotaFn_coe]

private def wcgapenUnitri (t : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, t; 0, 1], by rw [Matrix.det_fin_two_of]; simp⟩

private lemma wcgapenUnitri_mem (t : F) : wcgapenUnitri t ∈ unitriangular 2 F := by
  rw [mem_unitriangular]
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [wcgapenUnitri]
  · intro i
    fin_cases i <;> simp [wcgapenUnitri]

private lemma wcgapenEmbM_unitri (b c : F) (t : F) :
    wcgapenEmbM b c ((wcgapenUnitri t : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = fromBlocks 1 (t • wcgapenC b c) 0 1 := by
  rw [wcgapenEmbM]
  have h00 : ((wcgapenUnitri t : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by simp [wcgapenUnitri]
  have h01 : ((wcgapenUnitri t : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 0 1 = t := by simp [wcgapenUnitri]
  have h10 : ((wcgapenUnitri t : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simp [wcgapenUnitri]
  have h11 : ((wcgapenUnitri t : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by simp [wcgapenUnitri]
  rw [h00, h01, h10, h11]
  simp

private lemma wcgapenIotaFn_unitri (b c : F) (hc : c ≠ 0) [CharP F 2] (t : F) :
    wcgapenIotaFn b c hc (wcgapenUnitri t) = sp4Z (t * b) (t * c) := by
  apply statedSp_ext
  rw [wcgapenIotaFn_coe, wcgapenEmbM_unitri, sp4Z, coe_tau, Matrix.fromBlocks_inj]
  refine ⟨rfl, ?_, rfl, rfl⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wcgapenC, sym2, Matrix.smul_apply]

private lemma wcgapenIota_unitri (b c : F) (hc : c ≠ 0) [CharP F 2] (t : F) :
    wcgapenIota b c hc (wcgapenUnitri t) = sp4Z (t * b) (t * c) := by
  rw [wcgapenIota_apply]
  exact wcgapenIotaFn_unitri b c hc t

private lemma wcgapenIotaFn_unitri_of_mem (b c : F) (hc : c ≠ 0) [CharP F 2]
    {u : Matrix.SpecialLinearGroup (Fin 2) F} (hu : u ∈ unitriangular 2 F) :
    wcgapenIotaFn b c hc u =
      sp4Z ((u : Matrix (Fin 2) (Fin 2) F) 0 1 * b) ((u : Matrix (Fin 2) (Fin 2) F) 0 1 * c) := by
  have hu' : u = wcgapenUnitri ((u : Matrix (Fin 2) (Fin 2) F) 0 1) := by
    obtain ⟨hlo, hdiag⟩ := mem_unitriangular.mp hu
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j
    · simp [wcgapenUnitri, hdiag]
    · rfl
    · simpa [wcgapenUnitri] using hlo 1 0 (by decide)
    · simp [wcgapenUnitri, hdiag]
  conv_lhs => rw [hu']
  exact wcgapenIotaFn_unitri b c hc ((u : Matrix (Fin 2) (Fin 2) F) 0 1)

private lemma wcgapenIota_unitri_of_mem (b c : F) (hc : c ≠ 0) [CharP F 2]
    {u : Matrix.SpecialLinearGroup (Fin 2) F} (hu : u ∈ unitriangular 2 F) :
    wcgapenIota b c hc u =
      sp4Z ((u : Matrix (Fin 2) (Fin 2) F) 0 1 * b) ((u : Matrix (Fin 2) (Fin 2) F) 0 1 * c) := by
  rw [wcgapenIota_apply]
  exact wcgapenIotaFn_unitri_of_mem b c hc hu

private lemma wcgapenIotaFn_injective (b c : F) (hc : c ≠ 0) [CharP F 2] :
    Function.Injective (wcgapenIotaFn b c hc) := by
  intro g h hgh
  have hmat : wcgapenEmbM b c (g : Matrix (Fin 2) (Fin 2) F) =
      wcgapenEmbM b c (h : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun x : StatedSp 2 F =>
      (((x : GL (Fin 2 ⊕ Fin 2) F)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hgh
    rwa [wcgapenIotaFn_coe, wcgapenIotaFn_coe] at this
  have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = (h : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    have := congrFun (congrFun hmat (Sum.inl 0)) (Sum.inl 0)
    simpa [wcgapenEmbM, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply] using this
  have h01 : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = (h : Matrix (Fin 2) (Fin 2) F) 0 1 := by
    have := congrFun (congrFun hmat (Sum.inl 0)) (Sum.inr 1)
    simp only [wcgapenEmbM, Matrix.fromBlocks_apply₁₂, Matrix.smul_apply, wcgapenC_01] at this
    exact mul_right_cancel₀ hc this
  have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = (h : Matrix (Fin 2) (Fin 2) F) 1 0 := by
    have := congrFun (congrFun hmat (Sum.inr 0)) (Sum.inl 1)
    simp only [wcgapenEmbM, Matrix.fromBlocks_apply₂₁, Matrix.smul_apply,
      wcgapenCinv_01 b c hc] at this
    exact mul_right_cancel₀ (inv_ne_zero hc) this
  have h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = (h : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    have := congrFun (congrFun hmat (Sum.inr 1)) (Sum.inr 1)
    simpa [wcgapenEmbM, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply] using this
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

private lemma wcgapenIota_injective (b c : F) (hc : c ≠ 0) [CharP F 2] :
    Function.Injective (wcgapenIota b c hc) := by
  intro g h hgh
  apply wcgapenIotaFn_injective b c hc
  simpa [wcgapenIota_apply] using hgh

private lemma wcgapenEmbM_slTwoDiag (b c : F) (l : Fˣ) :
    wcgapenEmbM b c ((slTwoDiag l : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) =
      diagonal (Sum.elim (fun _ : Fin 2 => (l : F)) (fun _ : Fin 2 => ((l⁻¹ : Fˣ) : F))) := by
  rw [wcgapenEmbM]
  have h00 : ((slTwoDiag l : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 0 0 = (l : F) := by simp [slTwoDiag]
  have h01 : ((slTwoDiag l : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by simp [slTwoDiag]
  have h10 : ((slTwoDiag l : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simp [slTwoDiag]
  have h11 : ((slTwoDiag l : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 1 1 = ((l⁻¹ : Fˣ) : F) := by simp [slTwoDiag]
  rw [h00, h01, h10, h11, zero_smul, zero_smul, Matrix.smul_one_eq_diagonal,
    Matrix.smul_one_eq_diagonal, Matrix.fromBlocks_diagonal]

private lemma wcgapenIota_slTwoDiag (b c : F) (hc : c ≠ 0) [CharP F 2] (l : Fˣ) :
    wcgapenIota b c hc (slTwoDiag l) = torusHom (fun _ : Fin 2 => l) := by
  apply statedSp_ext
  simp only [wcgapenIota_coe, wcgapenEmbM_slTwoDiag, coe_torusHom]

private lemma wcgapen_map_eq_of_hA (b c : F) (hc : c ≠ 0) [CharP F 2]
    {A : Subgroup (StatedSp 2 F)}
    (hA : ∀ g, g ∈ A ↔ ∃ t : F, g = sp4Z (t * b) (t * c)) :
    A = (unitriangular 2 F).map (wcgapenIota b c hc) := by
  ext g
  rw [hA g]
  constructor
  · rintro ⟨t, rfl⟩
    exact Subgroup.mem_map.mpr ⟨wcgapenUnitri t, wcgapenUnitri_mem t, wcgapenIota_unitri b c hc t⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(u : Matrix (Fin 2) (Fin 2) F) 0 1, wcgapenIota_unitri_of_mem b c hc hu⟩

theorem sp4_emb_line {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) (b c : F) (hc : c ≠ 0)
    {A : Subgroup (StatedSp 2 F)} (hA : ∀ g, g ∈ A ↔ ∃ t : F, g = sp4Z (t * b) (t * c)) :
    Sp4Sl2Emb A := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hF]
    norm_num)
  refine ⟨wcgapenIota b c hc, wcgapenIota_injective b c hc,
    wcgapen_map_eq_of_hA b c hc hA, fun l => ?_⟩
  rw [wcgapenIota_slTwoDiag]
  exact (normal_subgroupOf_iff_le_normalizer
      (unipotent_le_borelSubgroup (r := 2) (K := F))).mp
    (unipotent_subgroupOf_borelSubgroup_normal (r := 2) (K := F))
    (torus_le_borelSubgroup (r := 2) (K := F) ⟨fun _ : Fin 2 => l, rfl⟩)

end

end CFSG.LocalAnalysis.WeakClosure81

end
