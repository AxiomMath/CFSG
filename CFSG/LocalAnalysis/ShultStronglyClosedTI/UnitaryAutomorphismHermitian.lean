module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismHyperbolic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_4

public section

namespace CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.BenderSuzuki.MatrixGroups

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def hypFinEquiv : HypIndex 1 1 ≃ Fin 3 where
  toFun
    | .inl _ => 0
    | .inr (.inl _) => 1
    | .inr (.inr _) => 2
  invFun i := ![.inl 0, .inr (.inl 0), .inr (.inr 0)] i
  left_inv := by rintro (i | i | i) <;> fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[expose] noncomputable def hypReindexGL : GL (HypIndex 1 1) K ≃* GL (Fin 3) K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K hypFinEquiv).toMulEquiv

theorem coe_hypReindexGL (g : GL (HypIndex 1 1) K) :
    (hypReindexGL g : Matrix (Fin 3) (Fin 3) K) =
      Matrix.reindex hypFinEquiv hypFinEquiv (g : Matrix (HypIndex 1 1) (HypIndex 1 1) K) :=
  rfl

theorem reindex_mul (A B : Matrix (HypIndex 1 1) (HypIndex 1 1) K) :
    Matrix.reindex hypFinEquiv hypFinEquiv (A * B) =
      Matrix.reindex hypFinEquiv hypFinEquiv A * Matrix.reindex hypFinEquiv hypFinEquiv B := by
  simp only [reindex_apply, submatrix_mul_equiv]

omit [Field K] in
theorem reindex_map (φ : K → K) (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) :
    (Matrix.reindex hypFinEquiv hypFinEquiv A).map φ =
      Matrix.reindex hypFinEquiv hypFinEquiv (A.map φ) := by
  simp only [reindex_apply, submatrix_map]

omit [Field K] in
theorem reindex_injective :
    Function.Injective (Matrix.reindex hypFinEquiv hypFinEquiv :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K → Matrix (Fin 3) (Fin 3) K) :=
  (Matrix.reindex hypFinEquiv hypFinEquiv).injective

theorem reindex_hypGram :
    Matrix.reindex hypFinEquiv hypFinEquiv (hypGram 1 1 K) = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypGram_apply, hypFinEquiv]

theorem glAut_hypReindexGL (σ : K ≃+* K) (g : GL (HypIndex 1 1) K) :
    glAut σ (hypReindexGL g) = hypReindexGL (glAut σ g) := by
  apply Units.ext
  rw [coe_glAut, coe_hypReindexGL, coe_hypReindexGL, coe_glAut, reindex_map]

variable (J : HermitianForm 3 K)

theorem conjTranspose_eq_transpose_map (h : UnitaryFieldData p f K)
    (hconj : ∀ c, J.conj c = h.bar c) (M : Matrix (Fin 3) (Fin 3) K) :
    J.conjTranspose M = (M.map h.bar)ᵀ := by
  ext i j
  simp [HermitianForm.conjTranspose, hconj]

variable {J}

theorem hypReindexGL_unitary_iff (h : UnitaryFieldData p f K) (hconj : ∀ c, J.conj c = h.bar c)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (g : GL (HypIndex 1 1) K) :
    hypReindexGL g ∈ J.unitarySubgroup ↔
      ((g : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map h.bar)ᵀ * hypGram 1 1 K *
        (g : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = hypGram 1 1 K := by
  rw [HermitianForm.mem_unitarySubgroup_iff, conjTranspose_eq_transpose_map J h hconj, hJ,
    ← reindex_hypGram, coe_hypReindexGL, reindex_map, transpose_reindex, ← reindex_mul,
    ← reindex_mul]
  exact reindex_injective.eq_iff

theorem hypReindexGL_mem_iff (h : UnitaryFieldData p f K) (hconj : ∀ c, J.conj c = h.bar c)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (g : GL (HypIndex 1 1) K) :
    hypReindexGL g ∈ J.specialSubgroup ↔ g ∈ hypSU h 1 1 := by
  have hdet : GeneralLinearGroup.det (hypReindexGL g) = 1 ↔
      (g : Matrix (HypIndex 1 1) (HypIndex 1 1) K).det = 1 := by
    rw [Units.ext_iff, GeneralLinearGroup.val_det_apply, coe_hypReindexGL, det_reindex_self,
      Units.val_one]
  have hU := hypReindexGL_unitary_iff h hconj hJ g
  rw [HermitianForm.mem_unitarySubgroup_iff] at hU
  rw [HermitianForm.mem_specialSubgroup_iff, hU, hdet, mem_hypSU]

@[expose] noncomputable def hypSUEquiv (h : UnitaryFieldData p f K)
    (hconj : ∀ c, J.conj c = h.bar c) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    hypSU h 1 1 ≃* J.specialSubgroup :=
  (hypReindexGL.subgroupMap (hypSU h 1 1)).trans (MulEquiv.subgroupCongr (by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hypReindexGL_mem_iff h hconj hJ g).mpr hg
    · intro hx
      refine ⟨hypReindexGL.symm x, (hypReindexGL_mem_iff h hconj hJ _).mp ?_,
        MulEquiv.apply_symm_apply _ _⟩
      rwa [MulEquiv.apply_symm_apply]))

theorem coe_hypSUEquiv (h : UnitaryFieldData p f K) (hconj : ∀ c, J.conj c = h.bar c)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (g : hypSU h 1 1) :
    ((hypSUEquiv h hconj hJ g : J.specialSubgroup) : GL (Fin 3) K) = hypReindexGL g :=
  rfl

variable (J) in
noncomputable abbrev psuMk : J.specialSubgroup →* ProjectiveSpecialUnitaryMatrixGroup J :=
  ProjGenLinGroup.mk.subgroupMap J.specialSubgroup

theorem psuMk_surjective : Function.Surjective (psuMk J) :=
  MonoidHom.subgroupMap_surjective _ _

theorem coe_psuMk (g : J.specialSubgroup) :
    ((psuMk J g : ProjectiveSpecialUnitaryMatrixGroup J) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (g : GL (Fin 3) K) :=
  rfl

theorem psuMk_eq_psuMk_iff {g g' : J.specialSubgroup} :
    psuMk J g = psuMk J g' ↔
      ∃ u : Kˣ, (g : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) u = g' := by
  rw [← ProjGenLinGroup.mk_eq_mk_iff, ← coe_psuMk, ← coe_psuMk, Subtype.coe_inj]

theorem psuMk_eq_one_iff {g : J.specialSubgroup} :
    psuMk J g = 1 ↔ ∃ u : Kˣ, GeneralLinearGroup.scalar (Fin 3) u = (g : GL (Fin 3) K) := by
  rw [← Subtype.coe_inj, coe_psuMk, Subgroup.coe_one, ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range]

theorem hypReindexGL_scalar (u : Kˣ) :
    hypReindexGL (GeneralLinearGroup.scalar (HypIndex 1 1) u) =
      GeneralLinearGroup.scalar (Fin 3) u := by
  apply Units.ext
  rw [coe_hypReindexGL, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar,
    scalar_apply, scalar_apply, reindex_apply, submatrix_diagonal_equiv]
  rfl

theorem mem_hypScalars_of_scalar (h : UnitaryFieldData p f K) {g : hypSU h 1 1} {u : Kˣ}
    (hg : GeneralLinearGroup.scalar (HypIndex 1 1) u = (g : GL (HypIndex 1 1) K)) :
    g ∈ hypScalars h 1 1 := by
  obtain ⟨hgram, hdet⟩ := mem_hypSU.mp g.2
  rw [← hg, GeneralLinearGroup.coe_scalar] at hgram hdet
  refine mem_normOneScalars.mpr ⟨u, ?_, ?_, hg.symm⟩
  · have h1 := congrFun (congrFun hgram (.inl 0)) (.inr (.inr 0))
    simpa [hypGram_apply, scalar_apply, Matrix.mul_apply, diagonal_apply, UnitaryFieldData.norm,
      mul_comm] using h1
  · rw [scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, card_hypIndex] at hdet
    exact Units.ext (by simpa using hdet)

@[expose] noncomputable def hypToPSU (h : UnitaryFieldData p f K)
    (hconj : ∀ c, J.conj c = h.bar c) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    hypSU h 1 1 →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (psuMk J).comp (hypSUEquiv h hconj hJ).toMonoidHom

theorem hypToPSU_surjective (h : UnitaryFieldData p f K) (hconj : ∀ c, J.conj c = h.bar c)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) : Function.Surjective (hypToPSU h hconj hJ) :=
  psuMk_surjective.comp (hypSUEquiv h hconj hJ).surjective

theorem ker_hypToPSU (h : UnitaryFieldData p f K) (hconj : ∀ c, J.conj c = h.bar c)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (hypToPSU h hconj hJ).ker = hypScalars h 1 1 := by
  ext g
  rw [MonoidHom.mem_ker]
  change psuMk J (hypSUEquiv h hconj hJ g) = 1 ↔ _
  rw [psuMk_eq_one_iff, coe_hypSUEquiv]
  constructor
  · rintro ⟨u, hu⟩
    refine mem_hypScalars_of_scalar h (u := u) (hypReindexGL.injective ?_)
    rw [hypReindexGL_scalar, hu]
  · intro hg
    obtain ⟨u, -, -, hu⟩ := mem_normOneScalars.mp hg
    exact ⟨u, by rw [hu, hypReindexGL_scalar]⟩

@[expose] noncomputable def hypPSUEquivPSU (h : UnitaryFieldData p f K)
    (hconj : ∀ c, J.conj c = h.bar c) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    hypPSU h 1 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  (QuotientGroup.quotientMulEquivOfEq (ker_hypToPSU h hconj hJ)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (hypToPSU_surjective h hconj hJ))

theorem hypPSUEquivPSU_hypProj (h : UnitaryFieldData p f K) (hconj : ∀ c, J.conj c = h.bar c)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (g : hypSU h 1 1) :
    hypPSUEquivPSU h hconj hJ (hypProj h 1 1 g) = psuMk J (hypSUEquiv h hconj hJ g) :=
  rfl

theorem exists_isometry_psu (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (hconj : ∀ c, J.conj c = h.bar c) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ (σ : K ≃+* K) (A : GL (Fin 3) K), A ∈ J.unitarySubgroup ∧
      ∀ g : J.specialSubgroup,
        ∃ hg : A * glAut σ (g : GL (Fin 3) K) * A⁻¹ ∈ J.specialSubgroup,
          β (psuMk J g) = psuMk J ⟨_, hg⟩ := by
  set Φ := hypPSUEquivPSU h hconj hJ
  obtain ⟨σ, B, hB, hBg⟩ := exists_isometry_hypPSU h hq ((Φ.trans β).trans Φ.symm)
  refine ⟨σ, hypReindexGL B, (hypReindexGL_unitary_iff h hconj hJ B).mpr hB, fun g' => ?_⟩
  set g := (hypSUEquiv h hconj hJ).symm g'
  have hg' : hypSUEquiv h hconj hJ g = g' := MulEquiv.apply_symm_apply _ _
  obtain ⟨hg, hα⟩ := hBg g
  have hconjB : hypReindexGL (B * glAut σ (g : GL (HypIndex 1 1) K) * B⁻¹) =
      hypReindexGL B * glAut σ (g' : GL (Fin 3) K) * (hypReindexGL B)⁻¹ := by
    rw [map_mul, map_mul, map_inv, ← hg', coe_hypSUEquiv, glAut_hypReindexGL]
  have hmem : hypReindexGL B * glAut σ (g' : GL (Fin 3) K) * (hypReindexGL B)⁻¹ ∈
      J.specialSubgroup := by
    rw [← hconjB]
    exact (hypReindexGL_mem_iff h hconj hJ _).mpr hg
  refine ⟨hmem, ?_⟩
  have h1 : psuMk J g' = Φ (hypProj h 1 1 g) := by
    rw [hypPSUEquivPSU_hypProj, hg']
  have h2 : Φ.symm (β (Φ (hypProj h 1 1 g))) = hypProj h 1 1 ⟨_, hg⟩ := hα
  rw [h1, ← Φ.apply_symm_apply (β (Φ (hypProj h 1 1 g))), h2, hypPSUEquivPSU_hypProj]
  exact congrArg (psuMk J) (Subtype.ext hconjB)

theorem unitaryFieldData_of_card {p f : ℕ} (hp : p.Prime) (hq : 2 < p ^ f)
    (hcard : Nat.card K = (p ^ f) ^ 2) : UnitaryFieldData p f K := by
  refine ⟨hp, ?_, by rw [hcard, ← pow_mul, mul_comm]⟩
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · simp at hq
  · exact hf

theorem exists_isometry_psu_of_card [Finite K] {p f : ℕ} (hp : p.Prime) (hq : 2 < p ^ f)
    (hcard : Nat.card K = (p ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = p ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ (σ : K ≃+* K) (A : GL (Fin 3) K), A ∈ J.unitarySubgroup ∧
      ∀ g : J.specialSubgroup,
        ∃ hg : A * glAut σ (g : GL (Fin 3) K) * A⁻¹ ∈ J.specialSubgroup,
          β (psuMk J g) = psuMk J ⟨_, hg⟩ := by
  have h := unitaryFieldData_of_card (K := K) hp hq hcard
  have hconj : ∀ c, J.conj c = h.bar c := fun c => by
    rw [CFSG.BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J (p ^ f) hcard hfixed,
      UnitaryFieldData.bar_apply]
  exact exists_isometry_psu h hq hconj hJ β

end CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
