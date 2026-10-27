module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalSp
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalPlanes
public import CFSG.GroupTheory.SylowPQMaximal.Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalSL2
import CFSG.GroupTheory.SylowPQMaximal.Extension

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

open Matrix CFSG.Open CFSG.GroupTheory

@[expose] noncomputable def spPlaneStab (K : Type) [Field K] : Subgroup (StatedSp 2 K) :=
  (planeMonomial K).comap
    ((spPlaneOrder.reindexGL K).symm.toMonoidHom.comp (StatedSp 2 K).subtype)

theorem mem_spPlaneStab {K : Type} [Field K] {y : StatedSp 2 K} :
    y ∈ spPlaneStab K ↔
      (spPlaneOrder.reindexGL K).symm (y : GL (Fin 2 ⊕ Fin 2) K) ∈ planeMonomial K :=
  Iff.rfl

section PlaneStab

variable {K : Type} [Field K]

private def quatTwo : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

private theorem transpose_mul_quatTwo (X : Matrix (Fin 2) (Fin 2) K) :
    Xᵀ * quatTwo * X = X.det • quatTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatTwo, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

private theorem det_eq_one_of_transpose_mul (A : Matrix (Fin 2) (Fin 2) K)
    (h : Aᵀ * quatTwo * A = quatTwo) : A.det = 1 := by
  have h' : (quatTwo : Matrix (Fin 2) (Fin 2) K) = A.det • (quatTwo : Matrix (Fin 2) (Fin 2) K) := by
    rw [← transpose_mul_quatTwo A, h]
  have h01 := congrFun (congrFun h' (0 : Fin 2)) (1 : Fin 2)
  have h1 : (1 : K) = A.det := by simpa [quatTwo] using h01
  exact h1.symm

private def IsPlaneDiag (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) : Prop :=
  M.toBlocks₁₂ = 0 ∧ M.toBlocks₂₁ = 0

private theorem isPlaneDiag_fromBlocks (A D : Matrix (Fin 2) (Fin 2) K) :
    IsPlaneDiag (fromBlocks A 0 0 D) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.toBlocks_fromBlocks₁₂]
  · rw [Matrix.toBlocks_fromBlocks₂₁]

private theorem isPlaneMonomial_of_isPlaneDiag {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h : IsPlaneDiag M) : IsPlaneMonomial M := Or.inl h

private theorem spPlaneGram_eq : spPlaneGram (K := K) = fromBlocks quatTwo 0 0 quatTwo := rfl

private theorem blocks_form_of_isPlaneDiag {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hdiag : IsPlaneDiag M) (hM : Mᵀ * spPlaneGram * M = spPlaneGram) :
    M.toBlocks₁₁ᵀ * quatTwo * M.toBlocks₁₁ = quatTwo ∧
      M.toBlocks₂₂ᵀ * quatTwo * M.toBlocks₂₂ = quatTwo := by
  obtain ⟨h12, h21⟩ := hdiag
  have hrep : M = fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [h12, h21]
  rw [hrep, spPlaneGram_eq, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at hM
  simp only [Matrix.transpose_zero, zero_mul, mul_zero, add_zero, zero_add] at hM
  rw [Matrix.fromBlocks_inj] at hM
  exact ⟨hM.1, hM.2.2.2⟩

private theorem blocks_form_of_isPlaneAnti {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h11 : M.toBlocks₁₁ = 0) (h22 : M.toBlocks₂₂ = 0)
    (hM : Mᵀ * spPlaneGram * M = spPlaneGram) :
    M.toBlocks₂₁ᵀ * quatTwo * M.toBlocks₂₁ = quatTwo ∧
      M.toBlocks₁₂ᵀ * quatTwo * M.toBlocks₁₂ = quatTwo := by
  have hrep : M = fromBlocks 0 M.toBlocks₁₂ M.toBlocks₂₁ 0 := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [h11, h22]
  rw [hrep, spPlaneGram_eq, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at hM
  simp only [Matrix.transpose_zero, zero_mul, mul_zero, add_zero, zero_add] at hM
  rw [Matrix.fromBlocks_inj] at hM
  exact ⟨hM.1, hM.2.2.2⟩

private theorem inv_eq_fromBlocks_diag {A D : Matrix (Fin 2) (Fin 2) K}
    (u : GL (Fin 2 ⊕ Fin 2) K) (hu : (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks A 0 0 D)
    (hA : IsUnit A.det) (hD : IsUnit D.det) :
    ((u⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks A⁻¹ 0 0 D⁻¹ := by
  have hmul : (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * fromBlocks A⁻¹ 0 0 D⁻¹ = 1 := by
    rw [hu, Matrix.fromBlocks_multiply, Matrix.mul_nonsing_inv A hA, Matrix.mul_nonsing_inv D hD]
    simp [Matrix.fromBlocks_one]
  have hmul' : fromBlocks A⁻¹ 0 0 D⁻¹ * (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    rw [hu, Matrix.fromBlocks_multiply, Matrix.nonsing_inv_mul A hA, Matrix.nonsing_inv_mul D hD]
    simp [Matrix.fromBlocks_one]
  calc ((u⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K)
      = 1 * ((u⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K) := (one_mul _).symm
    _ = (fromBlocks A⁻¹ 0 0 D⁻¹ * (u : Matrix _ _ K)) *
          ((u⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K) := by rw [hmul']
    _ = fromBlocks A⁻¹ 0 0 D⁻¹ * ((u : Matrix _ _ K) *
          ((u⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K)) := by rw [mul_assoc]
    _ = fromBlocks A⁻¹ 0 0 D⁻¹ * 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    _ = fromBlocks A⁻¹ 0 0 D⁻¹ := mul_one _

private theorem inv_eq_fromBlocks_anti {B C : Matrix (Fin 2) (Fin 2) K}
    (u : GL (Fin 2 ⊕ Fin 2) K) (hu : (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks 0 B C 0)
    (hB : IsUnit B.det) (hC : IsUnit C.det) :
    ((u⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks 0 C⁻¹ B⁻¹ 0 := by
  have hmul : (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * fromBlocks 0 C⁻¹ B⁻¹ 0 = 1 := by
    rw [hu, Matrix.fromBlocks_multiply, Matrix.mul_nonsing_inv B hB, Matrix.mul_nonsing_inv C hC]
    simp [Matrix.fromBlocks_one]
  have hmul' : fromBlocks 0 C⁻¹ B⁻¹ 0 * (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    rw [hu, Matrix.fromBlocks_multiply, Matrix.nonsing_inv_mul C hC, Matrix.nonsing_inv_mul B hB]
    simp [Matrix.fromBlocks_one]
  calc ((u⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K)
      = 1 * ((u⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K) := (one_mul _).symm
    _ = (fromBlocks 0 C⁻¹ B⁻¹ 0 * (u : Matrix _ _ K)) *
          ((u⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K) := by rw [hmul']
    _ = fromBlocks 0 C⁻¹ B⁻¹ 0 * ((u : Matrix _ _ K) *
          ((u⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K)) := by rw [mul_assoc]
    _ = fromBlocks 0 C⁻¹ B⁻¹ 0 * 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    _ = fromBlocks 0 C⁻¹ B⁻¹ 0 := mul_one _

private theorem isPlaneDiag_conj {P Q : GL (Fin 2 ⊕ Fin 2) K}
    (hPmono : IsPlaneMonomial (P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
    (hPform : (P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * spPlaneGram *
      (P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = spPlaneGram)
    (hQ : IsPlaneDiag (Q : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
    IsPlaneDiag ((P * Q * P⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  obtain ⟨hQ12, hQ21⟩ := hQ
  have hQrep : (Q : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks (Q : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁ 0 0
        (Q : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Q : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)]
    rw [hQ12, hQ21]
  rw [Units.val_mul, Units.val_mul]
  rcases hPmono with ⟨hP12, hP21⟩ | ⟨hP11, hP22⟩
  · have hPrep : (P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks (P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁ 0 0
          (P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₂ := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks (P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)]
      rw [hP12, hP21]
    obtain ⟨hA, hD⟩ := blocks_form_of_isPlaneDiag ⟨hP12, hP21⟩ hPform
    have hA1 : ((P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁).det = 1 :=
      det_eq_one_of_transpose_mul _ hA
    have hD1 : ((P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₂).det = 1 :=
      det_eq_one_of_transpose_mul _ hD
    have hPinv : ((P⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks ((P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁)⁻¹ 0 0
          ((P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₂)⁻¹ :=
      inv_eq_fromBlocks_diag P hPrep (by rw [hA1]; exact isUnit_one)
        (by rw [hD1]; exact isUnit_one)
    rw [hPrep, hQrep, hPinv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [mul_zero, zero_mul, add_zero]
    exact isPlaneDiag_fromBlocks _ _
  · have hPrep : (P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks 0 (P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₂
          (P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₁ 0 := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks (P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)]
      rw [hP11, hP22]
    obtain ⟨hC, hB⟩ := blocks_form_of_isPlaneAnti hP11 hP22 hPform
    have hB1 : ((P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₂).det = 1 :=
      det_eq_one_of_transpose_mul _ hB
    have hC1 : ((P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₁).det = 1 :=
      det_eq_one_of_transpose_mul _ hC
    have hPinv : ((P⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks 0 ((P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₁)⁻¹
          ((P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₂)⁻¹ 0 :=
      inv_eq_fromBlocks_anti P hPrep (by rw [hB1]; exact isUnit_one)
        (by rw [hC1]; exact isUnit_one)
    rw [hPrep, hQrep, hPinv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [mul_zero, zero_mul, add_zero, zero_add]
    exact isPlaneDiag_fromBlocks _ _

private theorem exists_planeDiag_of_isPlaneDiag {u : GL (Fin 2 ⊕ Fin 2) K}
    (hdiag : IsPlaneDiag (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
    (hform : (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * spPlaneGram *
      (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = spPlaneGram) :
    ∃ x : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K, planeDiag x = u := by
  obtain ⟨hA, hD⟩ := blocks_form_of_isPlaneDiag hdiag hform
  obtain ⟨h12, h21⟩ := hdiag
  have hA1 : ((u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁).det = 1 :=
    det_eq_one_of_transpose_mul _ hA
  have hD1 : ((u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₂).det = 1 :=
    det_eq_one_of_transpose_mul _ hD
  refine ⟨(⟨(u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁, hA1⟩,
    ⟨(u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₂, hD1⟩), ?_⟩
  apply Units.ext
  rw [coe_planeDiag]
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)]
  rw [h12, h21]

private theorem sl2_form (X : SpecialLinearGroup (Fin 2) K) :
    (X : Matrix (Fin 2) (Fin 2) K)ᵀ * quatTwo * (X : Matrix (Fin 2) (Fin 2) K) = quatTwo := by
  rw [transpose_mul_quatTwo, Matrix.SpecialLinearGroup.det_coe, one_smul]

private theorem sl2_blocks_form (X Y : SpecialLinearGroup (Fin 2) K) :
    (fromBlocks (X : Matrix (Fin 2) (Fin 2) K) 0 0 (Y : Matrix (Fin 2) (Fin 2) K))ᵀ *
      spPlaneGram * fromBlocks (X : Matrix (Fin 2) (Fin 2) K) 0 0 (Y : Matrix (Fin 2) (Fin 2) K) =
      spPlaneGram := by
  rw [spPlaneGram_eq, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, zero_mul, mul_zero, add_zero, zero_add]
  rw [sl2_form X, sl2_form Y]

private noncomputable def spPlaneStabDiagHom (K : Type) [Field K] :
    SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K →* spPlaneStab K where
  toFun x :=
    ⟨⟨(spPlaneOrder.reindexGL K) (planeDiag x),
        (reindexGL_spPlaneOrder_mem_statedSp_iff (planeDiag x)).mpr
          (sl2_blocks_form x.1 x.2)⟩,
      (mem_spPlaneStab (K := K)).mpr (by
        show (spPlaneOrder.reindexGL K).symm ((spPlaneOrder.reindexGL K) (planeDiag x)) ∈
          planeMonomial K
        rw [MulEquiv.symm_apply_apply]
        exact mem_planeMonomial.mpr
          (isPlaneMonomial_of_isPlaneDiag (isPlaneDiag_fromBlocks _ _)))⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    simp [map_mul]

private theorem val_spPlaneStabDiagHom
    (x : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) :
    (((spPlaneStabDiagHom K x : spPlaneStab K) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
      (spPlaneOrder.reindexGL K) (planeDiag x) := rfl

private noncomputable def planeStabGLHom (K : Type) [Field K] :
    spPlaneStab K →* GL (Fin 2 ⊕ Fin 2) K :=
  (spPlaneOrder.reindexGL K).symm.toMonoidHom.comp
    ((StatedSp 2 K).subtype.comp (spPlaneStab K).subtype)

private noncomputable def planeStabGL (y : spPlaneStab K) : GL (Fin 2 ⊕ Fin 2) K :=
  planeStabGLHom K y

private noncomputable def planeStabMat (y : spPlaneStab K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  (planeStabGL y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

private theorem planeStabGL_mul (y z : spPlaneStab K) :
    planeStabGL (y * z) = planeStabGL y * planeStabGL z :=
  map_mul _ y z

private theorem planeStabGL_inv (y : spPlaneStab K) :
    planeStabGL y⁻¹ = (planeStabGL y)⁻¹ :=
  map_inv _ y

private theorem isPlaneMonomial_planeStabMat (y : spPlaneStab K) :
    IsPlaneMonomial (planeStabMat y) :=
  (mem_spPlaneStab (K := K)).mp y.2

private theorem planeStabMat_form (y : spPlaneStab K) :
    (planeStabMat y)ᵀ * spPlaneGram * planeStabMat y = spPlaneGram := by
  refine (reindexGL_spPlaneOrder_mem_statedSp_iff (K := K) (planeStabGL y)).mp ?_
  change (spPlaneOrder.reindexGL K) ((spPlaneOrder.reindexGL K).symm
    (((y : spPlaneStab K) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K)) ∈ StatedSp 2 K
  rw [MulEquiv.apply_symm_apply]
  exact ((y : spPlaneStab K) : StatedSp 2 K).2

private theorem mem_range_spPlaneStabDiagHom_iff (y : spPlaneStab K) :
    y ∈ (spPlaneStabDiagHom K).range ↔ IsPlaneDiag (planeStabMat y) := by
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    rw [← hx]
    change IsPlaneDiag (((spPlaneOrder.reindexGL K).symm
      (((spPlaneStabDiagHom K x : spPlaneStab K) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    rw [val_spPlaneStabDiagHom, MulEquiv.symm_apply_apply, coe_planeDiag]
    exact isPlaneDiag_fromBlocks _ _
  · intro hy
    have hform := planeStabMat_form y
    obtain ⟨x, hx⟩ := exists_planeDiag_of_isPlaneDiag hy hform
    refine MonoidHom.mem_range.mpr ⟨x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [val_spPlaneStabDiagHom, hx]
    exact MulEquiv.apply_symm_apply (spPlaneOrder.reindexGL K) _

private theorem injective_spPlaneStabDiagHom :
    Function.Injective (spPlaneStabDiagHom K) := by
  intro x y hxy
  have h1 : (spPlaneOrder.reindexGL K) (planeDiag x) =
      (spPlaneOrder.reindexGL K) (planeDiag y) := by
    have h2 := congrArg (fun z : spPlaneStab K =>
      ((z : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K)) hxy
    rwa [val_spPlaneStabDiagHom, val_spPlaneStabDiagHom] at h2
  have h2 : planeDiag x = planeDiag y := (spPlaneOrder.reindexGL K).injective h1
  have h3 := congrArg (fun z : GL (Fin 2 ⊕ Fin 2) K =>
    (z : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h2
  rw [coe_planeDiag, coe_planeDiag, Matrix.fromBlocks_inj] at h3
  exact Prod.ext (Subtype.ext h3.1) (Subtype.ext h3.2.2.2)

private theorem normal_range_spPlaneStabDiagHom :
    ((spPlaneStabDiagHom K).range).Normal where
  conj_mem := by
    intro m hm g
    rw [mem_range_spPlaneStabDiagHom_iff] at hm ⊢
    have hgm : planeStabGL (g * m * g⁻¹) =
        planeStabGL g * planeStabGL m * (planeStabGL g)⁻¹ := by
      rw [planeStabGL_mul, planeStabGL_mul, planeStabGL_inv]
    change IsPlaneDiag ((planeStabGL (g * m * g⁻¹) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    rw [hgm]
    exact isPlaneDiag_conj (isPlaneMonomial_planeStabMat g) (planeStabMat_form g) hm

private theorem mul_self_mem_range_spPlaneStabDiagHom (y : spPlaneStab K) :
    y * y ∈ (spPlaneStabDiagHom K).range := by
  rw [mem_range_spPlaneStabDiagHom_iff]
  have hsq : planeStabMat (y * y) = planeStabMat y * planeStabMat y := by
    change ((planeStabGL (y * y) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((planeStabGL y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((planeStabGL y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    rw [planeStabGL_mul, Units.val_mul]
  rw [hsq]
  rcases (mem_spPlaneStab (K := K)).mp y.2 with hdiag | hanti
  · obtain ⟨h12, h21⟩ := hdiag
    have h12' : (planeStabMat y).toBlocks₁₂ = 0 := h12
    have h21' : (planeStabMat y).toBlocks₂₁ = 0 := h21
    have hrep : planeStabMat y =
        fromBlocks (planeStabMat y).toBlocks₁₁ 0 0 (planeStabMat y).toBlocks₂₂ := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks (planeStabMat y)]
      rw [h12', h21']
    rw [hrep, Matrix.fromBlocks_multiply]
    simp only [mul_zero, zero_mul, add_zero, zero_add]
    exact isPlaneDiag_fromBlocks _ _
  · obtain ⟨h11, h22⟩ := hanti
    have h11' : (planeStabMat y).toBlocks₁₁ = 0 := h11
    have h22' : (planeStabMat y).toBlocks₂₂ = 0 := h22
    have hrep : planeStabMat y =
        fromBlocks 0 (planeStabMat y).toBlocks₁₂ (planeStabMat y).toBlocks₂₁ 0 := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks (planeStabMat y)]
      rw [h11', h22']
    rw [hrep, Matrix.fromBlocks_multiply]
    simp only [mul_zero, zero_mul, add_zero, zero_add]
    exact isPlaneDiag_fromBlocks _ _

private theorem isPGroup_quotient_spPlaneStabDiagHom (K : Type) [Field K]
    [((spPlaneStabDiagHom K).range).Normal] :
    IsPGroup 2 (spPlaneStab K ⧸ (spPlaneStabDiagHom K).range) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro y
  have h1 : ((y ^ 2 : spPlaneStab K) : spPlaneStab K ⧸ (spPlaneStabDiagHom K).range) = 1 :=
    (QuotientGroup.eq_one_iff (y ^ 2)).mpr (by
      simpa [sq] using mul_self_mem_range_spPlaneStabDiagHom y)
  refine ⟨1, ?_⟩
  rw [pow_one, ← QuotientGroup.mk_pow]
  exact h1

private theorem charP_of_card_eq_prime {K : Type} [Field K] {q : ℕ} (hq : Nat.Prime q)
    (hK : Nat.card K = q) : CharP K q := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq.ne_zero)
  let hF : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hcard : Fintype.card K = q := by rw [← Nat.card_eq_fintype_card, hK]
  have hdvd : ringChar K ∣ q := by
    rw [← hcard, hn]
    exact dvd_pow_self _ n.ne_zero
  exact ringChar.of_eq ((Nat.prime_dvd_prime_iff_eq hp hq).1 hdvd)

private theorem two_ne_zero_of_card {K : Type} [Field K] (hK : Nat.card K = 3 ∨ Nat.card K = 5) :
    (2 : K) ≠ 0 := by
  rcases hK with h3 | h5
  · have : CharP K 3 := charP_of_card_eq_prime (by norm_num) h3
    intro h2
    exact (by norm_num : ¬ (3 ∣ 2)) ((CharP.cast_eq_zero_iff K 3 2).mp h2)
  · have : CharP K 5 := charP_of_card_eq_prime (by norm_num) h5
    intro h2
    exact (by norm_num : ¬ (5 ∣ 2)) ((CharP.cast_eq_zero_iff K 5 2).mp h2)

private theorem finite_of_card_eq {K : Type} [Field K] (hK : Nat.card K = 3 ∨ Nat.card K = 5) :
    Finite K :=
  Nat.finite_of_card_ne_zero (by rcases hK with h | h <;> rw [h] <;> norm_num)

private theorem ringChar_ne_two_of_card {K : Type} [Field K]
    (hK : Nat.card K = 3 ∨ Nat.card K = 5) : ringChar K ≠ 2 := by
  intro h
  have : CharP K 2 := ringChar.eq_iff.mp h
  exact two_ne_zero_of_card hK ((CharP.cast_eq_zero_iff K 2 2).mpr (dvd_refl 2))

end PlaneStab

theorem sylowPQMaximal_spPlaneStab {K : Type} [Field K] (hK : Nat.card K = 3 ∨ Nat.card K = 5) :
    SylowPQMaximal 2 5 (spPlaneStab K) := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have : Finite K := finite_of_card_eq hK
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (GL (Fin 2 ⊕ Fin 2) K) :=
    Fintype.ofInjective (fun u : GL (Fin 2 ⊕ Fin 2) K =>
      (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) (fun _ _ h => Units.ext h)
  have : Finite (GL (Fin 2 ⊕ Fin 2) K) := Finite.of_fintype _
  have : Finite (StatedSp 2 K) := inferInstance
  have : Finite (spPlaneStab K) := inferInstance
  have hEprod : SylowPQMaximal 2 5
      (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) :=
    SylowPQMaximal.prod (sylowPQMaximal_specialLinearGroup_two hK)
      (sylowPQMaximal_specialLinearGroup_two hK)
  have hE : SylowPQMaximal 2 5 ↥(spPlaneStabDiagHom K).range :=
    SylowPQMaximal.of_mulEquiv (MonoidHom.ofInjective injective_spPlaneStabDiagHom) hEprod
  have : ((spPlaneStabDiagHom K).range).Normal := normal_range_spPlaneStabDiagHom
  exact SylowPQMaximal.of_normal_of_isPGroup_quotient _
    hE (isPGroup_quotient_spPlaneStabDiagHom K)

private theorem glRep_injective_apply {K : Type} [Field K] (L : Type*) [Field L] [Algebra K L]
    (u : GL (Fin 2 ⊕ Fin 2) K) : Function.Injective (glRep L u) := by
  have h : ∀ v, glRep L u⁻¹ (glRep L u v) = v := by
    intro v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  exact Function.LeftInverse.injective h

private theorem submodule_map_conj {K : Type} [Field K] (L : Type*) [Field L] [Algebra K L]
    (A B : GL (Fin 2 ⊕ Fin 2) K) (W : Submodule L ((Fin 2 ⊕ Fin 2) → L)) :
    (W.map (glRep L A)).map (glRep L A * glRep L B * glRep L A⁻¹) =
      (W.map (glRep L B)).map (glRep L A) := by
  conv_lhs => rw [← Submodule.map_comp]
  conv_rhs => rw [← Submodule.map_comp]
  congr 1
  have hinv : (glRep L A⁻¹).comp (glRep L A) = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hinv' : ∀ v, glRep L A⁻¹ (glRep L A v) = v := by
    intro v
    rw [← LinearMap.comp_apply, hinv]
    rfl
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, Module.End.mul_apply]
  rw [hinv' v]

theorem sp4_isPGroup_of_blocks {K : Type} [Field K] (hK : Nat.card K = 3 ∨ Nat.card K = 5)
    (P : Sylow 2 (StatedSp 2 K)) (H : Subgroup (StatedSp 2 K))
    (hPH : (P : Subgroup (StatedSp 2 K)) ≤ H)
    (hH : CFSG.IsPiSubgroup {r : Nat.Primes | (r : ℕ) = 2 ∨ (r : ℕ) = 5} H)
    (L : Type*) [Field L] [Algebra K L] {κ : Type*} [Nontrivial κ]
    (W : κ → Submodule L ((Fin 2 ⊕ Fin 2) → L)) (hind : iSupIndep W) (htop : ⨆ i, W i = ⊤)
    (hW0 : ∀ i, W i ≠ ⊥)
    (hperm : ∀ h ∈ H, ∀ i, ∃ j,
      (W i).map (glRep L ((h : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K)) = W j) :
    IsPGroup 2 H := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have : Finite K := finite_of_card_eq hK
  have : Fintype K := Fintype.ofFinite K
  have hK2 : ringChar K ≠ 2 := ringChar_ne_two_of_card hK
  have : Fintype (GL (Fin 2 ⊕ Fin 2) K) :=
    Fintype.ofInjective (fun u : GL (Fin 2 ⊕ Fin 2) K =>
      (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) (fun _ _ h => Units.ext h)
  have : Finite (GL (Fin 2 ⊕ Fin 2) K) := Finite.of_fintype _
  have : Finite (StatedSp 2 K) := inferInstance
  have : Finite H := inferInstance
  by_cases h5 : 5 ∣ Nat.card H
  · obtain ⟨a, b, hab⟩ : ∃ a b : K, a ^ 2 + b ^ 2 = -1 :=
      (CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.odd_field_two_dimensional_quaternion_matrices
        (K := K) hK2).1
    have hspan := sp4_adjoin_eq_top (K := K) hK2 P H hPH
    let ρ : Representation L H ((Fin 2 ⊕ Fin 2) → L) :=
      (glRep L).comp ((StatedSp 2 K).subtype.comp H.subtype)
    have hρ : Function.Injective ρ := by
      intro x y hxy
      have h1 : glRep L (((x : H) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
          glRep L (((y : H) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := hxy
      exact Subtype.ext (Subtype.ext (glRep_injective (K := K) L h1))
    have hirr : ∀ U : Submodule L ((Fin 2 ⊕ Fin 2) → L),
        (∀ h : H, ∀ u ∈ U, ρ h u ∈ U) → U = ⊥ ∨ U = ⊤ := by
      intro U hU
      exact eq_bot_or_eq_top_of_adjoin_eq_top
        (fun h : H => (((h : H) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K)) hspan L U hU
    have hfin4 : Module.finrank L ((Fin 2 ⊕ Fin 2) → L) = 4 := by
      rw [Module.finrank_fintype_fun_eq_card L]
      simp [Fintype.card_sum]
    have hWdim : ∀ i : κ, Nat.card κ * Module.finrank L (W i) = 4 := by
      intro i
      have h := card_mul_finrank_eq_of_irreducible hirr hind htop hW0
        (fun h j => hperm h h.2 j) i
      rwa [hfin4] at h
    have hκdvd : Nat.card κ ∣ 4 := ⟨Module.finrank L (W (Classical.arbitrary κ)), (hWdim _).symm⟩
    have : Finite κ := finite_of_iSupIndep hind hW0
    have hκ2 : 2 ≤ Nat.card κ := Finite.one_lt_card
    have hκcases : Nat.card κ = 2 ∨ Nat.card κ = 4 := by
      have hdvd : Nat.card κ ∣ 2 ^ 2 := by
        have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
        rwa [← h4]
      rcases (Nat.dvd_prime_pow (p := 2) (by norm_num) (m := 2)).mp hdvd with ⟨k, hk, hkeq⟩
      interval_cases k <;> norm_num at hkeq
      · omega
      · left; omega
      · right; omega
    rcases hκcases with hκeq | hκeq
    · obtain ⟨g, hg⟩ :=
        exists_conj_mem_of_sylow_le (spP0_le_statedSp hab) (isPGroup_spP0 hab) P hPH
      let H' : Subgroup (StatedSp 2 K) := H.map (MulAut.conj g⁻¹).toMonoidHom
      let A : GL (Fin 2 ⊕ Fin 2) K := ((g⁻¹ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K)
      let W' : κ → Submodule L ((Fin 2 ⊕ Fin 2) → L) := fun i => (W i).map (glRep L A)
      have hspP0_le_H'' : spP0 hab ≤ H'.map (StatedSp 2 K).subtype := by
        intro x hx
        refine Subgroup.mem_map.mpr ⟨⟨x, spP0_le_statedSp hab hx⟩, ?_, rfl⟩
        have hconj : (MulAut.conj g⁻¹) (g * ⟨x, spP0_le_statedSp hab hx⟩ * g⁻¹) =
            ⟨x, spP0_le_statedSp hab hx⟩ := by
          rw [MulAut.conj_apply]
          group
        exact Subgroup.mem_map.mpr ⟨_, hg x hx, hconj⟩
      have hAinj : Function.Injective (glRep L A) := glRep_injective_apply L A
      have hind' : iSupIndep W' := LinearMap.iSupIndep_map _ hAinj hind
      have hW0' : ∀ i, W' i ≠ ⊥ := by
        intro i hi
        obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff (W i)).mp (hW0 i)
        have hmem : glRep L A v ∈ W' i := Submodule.mem_map_of_mem hv
        have hne : glRep L A v ≠ 0 := fun h => hv0 (hAinj (by rw [h, map_zero]))
        exact (Submodule.ne_bot_iff (W' i)).mpr ⟨_, hmem, hne⟩ hi
      have hperm' : ∀ x ∈ H'.map (StatedSp 2 K).subtype, ∀ i, ∃ j,
          (W' i).map (glRep L x) = W' j := by
        rintro x ⟨y, hy, rfl⟩ i
        obtain ⟨h, hh, hconj⟩ := Subgroup.mem_map.mp hy
        obtain ⟨j, hj⟩ := hperm h hh i
        refine ⟨j, ?_⟩
        have hyval : ((y : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
            A * ((h : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) * A⁻¹ := by
          rw [← hconj]
          show (((MulAut.conj g⁻¹) h : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
            A * ((h : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) * A⁻¹
          rw [MulAut.conj_apply]
          simp [A]
        show ((W i).map (glRep L A)).map (glRep L ((y : StatedSp 2 K) : GL _ K)) =
          (W j).map (glRep L A)
        rw [hyval, map_mul, map_mul]
        exact (submodule_map_conj L A _ (W i)).trans (by rw [hj])
      have hH'le : H' ≤ spPlaneStab K := by
        intro y hy
        rw [mem_spPlaneStab]
        exact symm_reindexGL_mem_planeMonomial spPlaneOrder hK2 hab hspP0_le_H'' L hind' hW0'
          hκeq hperm' (Subgroup.mem_map_of_mem _ hy)
      let P' : Sylow 2 (StatedSp 2 K) :=
        Sylow.mapSurjective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).surjective P
      have hP'coe : (P' : Subgroup (StatedSp 2 K)) =
          (P : Subgroup (StatedSp 2 K)).map (MulAut.conj g⁻¹).toMonoidHom :=
        Sylow.coe_mapSurjective (f := (MulAut.conj g⁻¹).toMonoidHom)
          (MulAut.conj g⁻¹).surjective P
      have hP'le : (P' : Subgroup (StatedSp 2 K)) ≤ H' := by
        rw [hP'coe]
        exact Subgroup.map_mono hPH
      have hH'le' : (P' : Subgroup (StatedSp 2 K)) ≤ spPlaneStab K := hP'le.trans hH'le
      have hHpi : CFSG.IsPiSubgroup {r : Nat.Primes | (r : ℕ) = 2 ∨ (r : ℕ) = 5}
          (H'.subgroupOf (spPlaneStab K)) := by
        have hcard : Nat.card ↥(H'.subgroupOf (spPlaneStab K)) = Nat.card ↥H := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH'le).toEquiv,
            Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
        intro r hr
        exact hH r (hcard ▸ hr)
      have hsub : ((P'.subtype hH'le' : Sylow 2 (spPlaneStab K)) : Subgroup (spPlaneStab K)) ≤
          H'.subgroupOf (spPlaneStab K) := by
        rw [Sylow.coe_subtype]
        exact Subgroup.subgroupOf_mono _ hP'le
      have hp : IsPGroup 2 ↥(H'.subgroupOf (spPlaneStab K)) :=
        sylowPQMaximal_spPlaneStab hK (P'.subtype hH'le') _ hsub hHpi
      have hH'p : IsPGroup 2 H' := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hH'le)
      exact hH'p.of_equiv
        (Subgroup.equivMapOfInjective H (MulAut.conj g⁻¹).toMonoidHom
          (MulAut.conj g⁻¹).injective).symm
    · have hline : ∀ i : κ, Module.finrank L (W i) = 1 := by
        intro i
        have h := hWdim i
        rw [hκeq] at h
        omega
      have hO : ∀ A : Subgroup H, A.Normal → IsPGroup 5 A → A = ⊥ := by
        intro A hA hA5
        have := hA
        rcases hK with h3 | h5'
        · exact sp4_three_eq_bot_of_normal_five h3 P H hPH hA5
        · exact sp4_five_eq_bot_of_normal_five h5' P H hPH hA5
      exact absurd h5 (not_dvd_card_of_finrank_eq_one hρ hind htop hW0
        (fun h j => hperm h h.2 j) hline Nat.prime_five (by omega) hO)
  · have huniq : ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 := by
      intro r hr hrH
      rcases (isPiSubgroup_pair_iff.mp hH) r hr hrH with h | h
      · exact h
      · exact absurd (h ▸ hrH) h5
    exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      (fun {d} hd hdvd => huniq d hd hdvd))

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural
