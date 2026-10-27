module

public import CFSG.Quasithin.SteinbergBSLinearThreeRoot

public section

namespace CFSG.Quasithin.F134.LieL3

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.Quasithin.SteinbergBS CFSG.ComponentClassification
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem isUpperTriangular_of_mem {g : SL(3, K)} (hg : g ∈ upperTriangular 3 K) :
    (g : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular :=
  mem_upperTriangular_iff_isUpperTriangular.mp hg

theorem diag_ne_zero_of_mem {g : SL(3, K)} (hg : g ∈ upperTriangular 3 K) (i : Fin 3) :
    (g : Matrix (Fin 3) (Fin 3) K) i i ≠ 0 :=
  left_ne_zero_of_mul_eq_one
    (coe_inv_apply_self_of_isUpperTriangular (isUpperTriangular_of_mem hg) i)

@[expose] noncomputable def diagUnit (i : Fin 3) : upperTriangular 3 K →* Kˣ where
  toFun g := Units.mk0 _ (diag_ne_zero_of_mem g.2 i)
  map_one' := by
    ext
    simp
  map_mul' g h := by
    ext
    simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul]
    exact mul_apply_self_of_isUpperTriangular (isUpperTriangular_of_mem g.2)
      (isUpperTriangular_of_mem h.2) i

theorem coe_diagUnit (i : Fin 3) (g : upperTriangular 3 K) :
    (diagUnit i g : K) = ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) i i :=
  rfl

@[expose] noncomputable def firstRatio : upperTriangular 3 K →* Kˣ :=
  diagUnit 0 * (diagUnit 1)⁻¹

@[expose] noncomputable def secondRatio : upperTriangular 3 K →* Kˣ :=
  diagUnit 1 * (diagUnit 2)⁻¹

@[expose] noncomputable def ratioHom : upperTriangular 3 K →* Kˣ :=
  firstRatio * secondRatio⁻¹

theorem diagUnit_scalar (i j : Fin 3) {z : SL(3, K)} (hz : z ∈ scalars 3 K) :
    diagUnit i ⟨z, scalars_le_upperTriangular 3 K hz⟩ =
      diagUnit j ⟨z, scalars_le_upperTriangular 3 K hz⟩ := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hz
  ext
  rw [coe_diagUnit, coe_diagUnit]
  change (z : Matrix (Fin 3) (Fin 3) K) i i = (z : Matrix (Fin 3) (Fin 3) K) j j
  rw [hc]
  simp

theorem firstRatio_scalar {z : SL(3, K)} (hz : z ∈ scalars 3 K) :
    firstRatio ⟨z, scalars_le_upperTriangular 3 K hz⟩ = 1 := by
  rw [firstRatio, MonoidHom.mul_apply, MonoidHom.inv_apply, diagUnit_scalar 0 1 hz,
    mul_inv_cancel]

theorem secondRatio_scalar {z : SL(3, K)} (hz : z ∈ scalars 3 K) :
    secondRatio ⟨z, scalars_le_upperTriangular 3 K hz⟩ = 1 := by
  rw [secondRatio, MonoidHom.mul_apply, MonoidHom.inv_apply, diagUnit_scalar 1 2 hz,
    mul_inv_cancel]

theorem ratioHom_scalar {z : SL(3, K)} (hz : z ∈ scalars 3 K) :
    ratioHom ⟨z, scalars_le_upperTriangular 3 K hz⟩ = 1 := by
  rw [ratioHom, MonoidHom.mul_apply, MonoidHom.inv_apply, firstRatio_scalar hz,
    secondRatio_scalar hz, inv_one, mul_one]

theorem eq_of_proj_eq (φ : upperTriangular 3 K →* Kˣ)
    (hφ : ∀ z (hz : z ∈ scalars 3 K), φ ⟨z, scalars_le_upperTriangular 3 K hz⟩ = 1)
    {g g' : SL(3, K)} (hg : g ∈ upperTriangular 3 K) (hg' : g' ∈ upperTriangular 3 K)
    (h : proj 3 K g = proj 3 K g') : φ ⟨g, hg⟩ = φ ⟨g', hg'⟩ := by
  have hz : g⁻¹ * g' ∈ scalars 3 K := proj_eq_proj_iff.mp h
  have he : (⟨g', hg'⟩ : upperTriangular 3 K) =
      ⟨g, hg⟩ * ⟨g⁻¹ * g', scalars_le_upperTriangular 3 K hz⟩ :=
    Subtype.ext (by simp)
  rw [he, map_mul, hφ _ hz, mul_one]

@[expose] def ratioTriangular (K : Type) [Field K] : Subgroup SL(3, K) where
  carrier := {g | g ∈ upperTriangular 3 K ∧
    (g : Matrix (Fin 3) (Fin 3) K) 0 0 * (g : Matrix (Fin 3) (Fin 3) K) 2 2 =
      (g : Matrix (Fin 3) (Fin 3) K) 1 1 ^ 2}
  one_mem' := ⟨(upperTriangular 3 K).one_mem, by simp⟩
  mul_mem' := by
    rintro g h ⟨hgB, hg⟩ ⟨hhB, hh⟩
    refine ⟨(upperTriangular 3 K).mul_mem hgB hhB, ?_⟩
    have hd := fun i => mul_apply_self_of_isUpperTriangular (isUpperTriangular_of_mem hgB)
      (isUpperTriangular_of_mem hhB) i
    show ((g : Matrix (Fin 3) (Fin 3) K) * h) 0 0 * ((g : Matrix (Fin 3) (Fin 3) K) * h) 2 2 =
      ((g : Matrix (Fin 3) (Fin 3) K) * h) 1 1 ^ 2
    rw [hd, hd, hd]
    linear_combination ((h : Matrix (Fin 3) (Fin 3) K) 0 0 * (h : Matrix (Fin 3) (Fin 3) K) 2 2) *
      hg + (g : Matrix (Fin 3) (Fin 3) K) 1 1 ^ 2 * hh
  inv_mem' := by
    rintro g ⟨hgB, hg⟩
    refine ⟨(upperTriangular 3 K).inv_mem hgB, ?_⟩
    have he := fun i => coe_inv_apply_self_of_isUpperTriangular (isUpperTriangular_of_mem hgB) i
    have h1 : (g : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 := diag_ne_zero_of_mem hgB 1
    have key : (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0 *
        ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2 -
        ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 1 1 ^ 2) *
        (g : Matrix (Fin 3) (Fin 3) K) 1 1 ^ 2 = 0 := by
      linear_combination (-(((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 0 *
        ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2)) * hg +
        ((g : Matrix (Fin 3) (Fin 3) K) 2 2 * ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2) *
          he 0 + he 2 -
        ((g : Matrix (Fin 3) (Fin 3) K) 1 1 * ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 1 1 +
          1) * he 1
    exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right (pow_ne_zero 2 h1))

@[expose] def ratioGroup (K : Type) [Field K] : Subgroup (projectiveSL 3 K) :=
  (ratioTriangular K).map (proj 3 K)

theorem ratioHom_eq_one_iff {g : SL(3, K)} (hg : g ∈ upperTriangular 3 K) :
    ratioHom ⟨g, hg⟩ = 1 ↔ g ∈ ratioTriangular K := by
  have h0 := diag_ne_zero_of_mem hg 0
  have h1 := diag_ne_zero_of_mem hg 1
  have h2 := diag_ne_zero_of_mem hg 2
  rw [ratioHom, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one, firstRatio,
    secondRatio, MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply,
    MonoidHom.inv_apply, Units.ext_iff, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_inv_eq_inv_val, coe_diagUnit, coe_diagUnit, coe_diagUnit]
  change _ ↔ g ∈ upperTriangular 3 K ∧ _
  simp only [hg, true_and]
  constructor
  · intro h
    field_simp at h
    linear_combination h
  · intro h
    field_simp
    linear_combination h

theorem ratioHom_eq_one_of_proj_mem {g : SL(3, K)} (hg : g ∈ upperTriangular 3 K)
    (h : proj 3 K g ∈ ratioGroup K) : ratioHom ⟨g, hg⟩ = 1 := by
  obtain ⟨g', hg', hgg'⟩ := h
  rw [eq_of_proj_eq ratioHom (fun z hz => ratioHom_scalar hz) hg hg'.1 hgg'.symm,
    ratioHom_eq_one_iff]
  exact hg'

theorem slConjugation_upper {A : GL (Fin 3) K}
    (hA : ∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) {M : SL(3, K)}
    (hM : M ∈ upperTriangular 3 K) :
    CatalogueBHigherLinearAction.slConjugation 3 K A M ∈ upperTriangular 3 K ∧
      ∀ i, (CatalogueBHigherLinearAction.slConjugation 3 K A M : Matrix (Fin 3) (Fin 3) K) i i =
        (M : Matrix (Fin 3) (Fin 3) K) i i := by
  have hA' : (A : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := fun _ _ h => hA _ _ h
  have hAi : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular := by
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hA'
  have hM' := isUpperTriangular_of_mem hM
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [coe_slConjugation]
    exact (hA'.mul hM').mul hAi hij
  · have h1 : (A : Matrix (Fin 3) (Fin 3) K) * ((A⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 := mul_apply_self_of_isUpperTriangular hA' hAi i
    rw [h1, one_apply_eq] at h2
    rw [coe_slConjugation, mul_apply_self_of_isUpperTriangular (hA'.mul hM') hAi,
      mul_apply_self_of_isUpperTriangular hA' hM']
    linear_combination (M : Matrix (Fin 3) (Fin 3) K) i i * h2.symm

theorem semilinear_mem_ratioGroup {A : GL (Fin 3) K}
    (hA : ∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) (σ : K ≃+* K)
    {x : projectiveSL 3 K} (hx : x ∈ ratioGroup K) :
    (conjAut 3 K A * fieldAut 3 K σ) x ∈ ratioGroup K := by
  obtain ⟨g, ⟨hgB, hg⟩, rfl⟩ := hx
  set M := SpecialLinearGroup.map σ.toRingHom g with hM
  have hMc : ∀ i j, (M : Matrix (Fin 3) (Fin 3) K) i j = σ ((g : Matrix (Fin 3) (Fin 3) K) i j) :=
    fun i j => by
      rw [hM, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      rfl
  have hMB : M ∈ upperTriangular 3 K := fun i j hij => by rw [hMc, hgB i j hij, map_zero]
  obtain ⟨hCB, hCd⟩ := slConjugation_upper hA hMB
  refine ⟨CatalogueBHigherLinearAction.slConjugation 3 K A M, ⟨hCB, ?_⟩, ?_⟩
  · rw [hCd, hCd, hCd, hMc, hMc, hMc, ← map_mul, ← map_pow, hg]
  · rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj]

theorem wJMat_transpose_wJMat_apply (M : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (wJMat * Mᵀ * wJMat : Matrix (Fin 3) (Fin 3) K) i j = M (Fin.rev j) (Fin.rev i) := by
  fin_cases i <;> fin_cases j <;>
    simp [wJMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]

theorem gammaZero_mem_ratioGroup [CharP K 2] {x : projectiveSL 3 K} (hx : x ∈ ratioGroup K) :
    gammaZero K x ∈ ratioGroup K := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨hiB, hi⟩ := (ratioTriangular K).inv_mem hg
  set h := CatalogueBHigherLinearAction.slConjugation 3 K (SpecialLinearGroup.toGL wJ)
    g⁻¹.transpose with hh
  have h2 : (((SpecialLinearGroup.toGL (wJ : SL(3, K)))⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = wJMat := by
    rw [← map_inv, wJ_inv]
    rfl
  have h1 : ((SpecialLinearGroup.toGL (wJ : SL(3, K)) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = wJMat := rfl
  have hent : ∀ i j : Fin 3, (h : Matrix (Fin 3) (Fin 3) K) i j =
      ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) (Fin.rev j) (Fin.rev i) := by
    intro i j
    rw [hh, coe_slConjugation, h1, h2, SpecialLinearGroup.coe_transpose,
      wJMat_transpose_wJMat_apply]
  refine ⟨h, ⟨fun i j hij => ?_, ?_⟩, ?_⟩
  · rw [hent]
    exact hiB _ _ (Fin.rev_lt_rev.mpr hij)
  · have r0 : Fin.rev (0 : Fin 3) = 2 := rfl
    have r1 : Fin.rev (1 : Fin 3) = 1 := rfl
    have r2 : Fin.rev (2 : Fin 3) = 0 := rfl
    rw [hent, hent, hent, r0, r1, r2, mul_comm]
    exact hi
  · rw [hh, gammaZero, MulAut.mul_apply, dualAut_proj, conjAut_proj]

theorem map_mem_ratioGroup [Finite K] [CharP K 2] {α : MulAut (projectiveSL 3 K)}
    (hα : (projUnitriangular 3 K).map α.toMonoidHom = projUnitriangular 3 K)
    {x : projectiveSL 3 K} (hx : x ∈ ratioGroup K) : α x ∈ ratioGroup K := by
  by_cases hs : α ∈ semilinearAutGroup 3 K
  · obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp hs
    exact semilinear_mem_ratioGroup (upperTriangular_of_semilinear_normalizes hα) σ hx
  · obtain ⟨A, σ, hA, rfl⟩ := exists_eq_semilinear_mul_gammaZero hα hs
    rw [MulAut.mul_apply]
    exact semilinear_mem_ratioGroup hA σ (gammaZero_mem_ratioGroup hx)

theorem proj_mem_projUnitriangular {g : SL(3, K)} (hg : g ∈ upperTriangular 3 K)
    (h01 : (g : Matrix (Fin 3) (Fin 3) K) 0 0 = (g : Matrix (Fin 3) (Fin 3) K) 1 1)
    (h12 : (g : Matrix (Fin 3) (Fin 3) K) 1 1 = (g : Matrix (Fin 3) (Fin 3) K) 2 2) :
    proj 3 K g ∈ projUnitriangular 3 K := by
  set c : Kˣ := diagUnit 0 ⟨g, hg⟩ with hcdef
  have hc : (c : K) = (g : Matrix (Fin 3) (Fin 3) K) 0 0 := rfl
  have hdet : (c : K) ^ 3 = 1 := by
    have h := g.2
    rw [Matrix.det_of_isUpperTriangular (isUpperTriangular_of_mem hg), Fin.prod_univ_three] at h
    rw [hc]
    linear_combination h + ((g : Matrix (Fin 3) (Fin 3) K) 0 0 ^ 2 +
      (g : Matrix (Fin 3) (Fin 3) K) 0 0 * (g : Matrix (Fin 3) (Fin 3) K) 2 2) * h01 +
      (g : Matrix (Fin 3) (Fin 3) K) 0 0 ^ 2 * h12
  have hc3 : c⁻¹ ^ 3 = 1 := by
    rw [inv_pow, inv_eq_one, Units.ext_iff, Units.val_pow_eq_pow_val, hdet, Units.val_one]
  have hz := scalarElement_mem_scalars c⁻¹ hc3
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  refine ⟨g * scalarElement c⁻¹ hc3, ⟨fun i j hij => ?_, fun i => ?_⟩, ?_⟩
  · show ((g : Matrix (Fin 3) (Fin 3) K) *
      (scalarElement c⁻¹ hc3 : Matrix (Fin 3) (Fin 3) K)) i j = 0
    rw [coe_scalarElement, scalar_apply, mul_diagonal, hg i j hij, zero_mul]
  · show ((g : Matrix (Fin 3) (Fin 3) K) *
      (scalarElement c⁻¹ hc3 : Matrix (Fin 3) (Fin 3) K)) i i = 1
    rw [coe_scalarElement, scalar_apply, mul_diagonal, Units.val_inv_eq_inv_val]
    have : (g : Matrix (Fin 3) (Fin 3) K) i i = c := by
      rw [hc]
      fin_cases i
      · rfl
      · exact h01.symm
      · exact (h01.trans h12).symm
    rw [this, mul_inv_cancel₀ hc0]
  · rw [map_mul, proj_eq_one_iff.mpr hz, mul_one]

theorem card_le_three [Finite K] {Q : Subgroup (projectiveSL 3 K)}
    (φ : upperTriangular 3 K →* Kˣ)
    (hφ : ∀ z (hz : z ∈ scalars 3 K), φ ⟨z, scalars_le_upperTriangular 3 K hz⟩ = 1)
    (hQB : ∀ g : SL(3, K), proj 3 K g ∈ Q → g ∈ upperTriangular 3 K)
    (hexp : ∀ x ∈ Q, x ^ 3 = 1)
    (hker : ∀ g (hg : g ∈ upperTriangular 3 K), proj 3 K g ∈ Q → φ ⟨g, hg⟩ = 1 →
      proj 3 K g = 1) :
    Nat.card Q ≤ 3 := by
  classical
  choose lift hlift using fun x : Q => proj_surjective 3 K (x : projectiveSL 3 K)
  have hB : ∀ x : Q, lift x ∈ upperTriangular 3 K := fun x => hQB _ (by rw [hlift]; exact x.2)
  have hroot : ∀ x : Q, φ ⟨lift x, hB x⟩ ^ 3 = 1 := by
    intro x
    have hz : lift x ^ 3 ∈ scalars 3 K := by
      rw [← proj_eq_one_iff, map_pow, hlift]
      exact hexp _ x.2
    rw [← map_pow]
    have he : (⟨lift x, hB x⟩ : upperTriangular 3 K) ^ 3 =
        ⟨lift x ^ 3, scalars_le_upperTriangular 3 K hz⟩ := Subtype.ext (by simp)
    rw [he, hφ _ hz]
  let f : Q → rootsOfUnity 3 K := fun x => ⟨φ ⟨lift x, hB x⟩, (mem_rootsOfUnity 3 _).mpr (hroot x)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hxy' : φ ⟨lift x, hB x⟩ = φ ⟨lift y, hB y⟩ := congrArg Subtype.val hxy
    have hmem : lift x * (lift y)⁻¹ ∈ upperTriangular 3 K := mul_mem (hB x) (inv_mem (hB y))
    have hproj : proj 3 K (lift x * (lift y)⁻¹) =
        (x : projectiveSL 3 K) * (y : projectiveSL 3 K)⁻¹ := by
      rw [map_mul, map_inv, hlift, hlift]
    have h1 : φ ⟨lift x * (lift y)⁻¹, hmem⟩ = 1 := by
      have he : (⟨lift x * (lift y)⁻¹, hmem⟩ : upperTriangular 3 K) =
          ⟨lift x, hB x⟩ * (⟨lift y, hB y⟩)⁻¹ := rfl
      rw [he, map_mul, map_inv, hxy', mul_inv_cancel]
    have h2 := hker _ hmem (by rw [hproj]; exact mul_mem x.2 (inv_mem y.2)) h1
    rw [hproj, mul_inv_eq_one] at h2
    exact Subtype.ext h2
  exact (Nat.card_le_card_of_injective f hf).trans (card_rootsOfUnity K 3)

theorem inf_projUnitriangular_eq_bot [Finite K] [CharP K 2] {Q : Subgroup (projectiveSL 3 K)}
    (hQ : Nat.card Q = 9) : Q ⊓ projUnitriangular 3 K = ⊥ := by
  have := Fintype.ofFinite K
  obtain ⟨k, -, hk⟩ := FiniteField.card K 2
  rw [← Nat.card_eq_fintype_card] at hk
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [hQ, card_projUnitriangular, hk, ← pow_mul]
  exact Nat.Coprime.pow_right _ (by norm_num)

theorem inf_ratioGroup_ne_bot [Finite K] [CharP K 2] {Q : Subgroup (projectiveSL 3 K)}
    (hQB : ∀ g : SL(3, K), proj 3 K g ∈ Q → g ∈ upperTriangular 3 K) (hQ : Nat.card Q = 9)
    (hexp : ∀ x ∈ Q, x ^ 3 = 1) : Q ⊓ ratioGroup K ≠ ⊥ := by
  intro hbot
  have := card_le_three ratioHom (fun z hz => ratioHom_scalar hz) hQB hexp
    (fun g hg hgQ h1 => by
      have hN : proj 3 K g ∈ Q ⊓ ratioGroup K :=
        ⟨hgQ, ⟨g, (ratioHom_eq_one_iff hg).mp h1, rfl⟩⟩
      rw [hbot] at hN
      exact hN)
  omega

theorem not_le_ratioGroup [Finite K] [CharP K 2] {Q : Subgroup (projectiveSL 3 K)}
    (hQB : ∀ g : SL(3, K), proj 3 K g ∈ Q → g ∈ upperTriangular 3 K) (hQ : Nat.card Q = 9)
    (hexp : ∀ x ∈ Q, x ^ 3 = 1) : ¬ Q ≤ ratioGroup K := by
  intro hle
  have hQU := inf_projUnitriangular_eq_bot hQ
  have := card_le_three firstRatio (fun z hz => firstRatio_scalar hz) hQB hexp
    (fun g hg hgQ h1 => by
      have hr := ratioHom_eq_one_of_proj_mem hg (hle hgQ)
      rw [ratioHom, MonoidHom.mul_apply, MonoidHom.inv_apply, h1, one_mul, inv_eq_one,
        secondRatio, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one, Units.ext_iff,
        coe_diagUnit, coe_diagUnit] at hr
      rw [firstRatio, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one, Units.ext_iff,
        coe_diagUnit, coe_diagUnit] at h1
      have hU : proj 3 K g ∈ Q ⊓ projUnitriangular 3 K :=
        ⟨hgQ, proj_mem_projUnitriangular hg h1 hr⟩
      rw [hQU] at hU
      exact hU)
  omega

end CFSG.Quasithin.F134.LieL3
