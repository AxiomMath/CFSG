module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoFlag
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.StandardType.RCKRP

open scoped Matrix

open CFSG.StandardType.ClassicalPosition

private def rckRPdp_B {ι F : Type} [Fintype ι] [Field F] (σ : F →+* F) (G : Matrix ι ι F)
    (u v : ι → F) : F :=
  dotProduct (fun i => σ (u i)) (G *ᵥ v)

private def rckRPdp_perp {ι F : Type} [Fintype ι] [Field F] (σ : F →+* F)
    (G : Matrix ι ι F) (U : Submodule F (ι → F)) : Submodule F (ι → F) where
  carrier := {v | ∀ u ∈ U, rckRPdp_B σ G u v = 0}
  zero_mem' := by
    intro u _
    simp [rckRPdp_B]
  add_mem' {v w} hv hw := by
    intro u hu
    simp only [rckRPdp_B, Matrix.mulVec_add, dotProduct_add]
    have hv' : (fun i => σ (u i)) ⬝ᵥ (G *ᵥ v) = 0 := hv u hu
    have hw' : (fun i => σ (u i)) ⬝ᵥ (G *ᵥ w) = 0 := hw u hu
    rw [hv', hw', add_zero]
  smul_mem' c v hv := by
    intro u hu
    simp only [rckRPdp_B, Matrix.mulVec_smul, dotProduct_smul]
    have hv' : (fun i => σ (u i)) ⬝ᵥ (G *ᵥ v) = 0 := hv u hu
    rw [hv', smul_zero]

@[simp] private theorem rckRPdp_mem_perp {ι F : Type} [Fintype ι] [Field F]
    {σ : F →+* F} {G : Matrix ι ι F} {U : Submodule F (ι → F)} {v : ι → F} :
    v ∈ rckRPdp_perp σ G U ↔ ∀ u ∈ U, rckRPdp_B σ G u v = 0 := Iff.rfl

private lemma rckRPdp_sigma_mulVec {ι F : Type} [Fintype ι] [Field F] (σ : F →+* F)
    (M : Matrix ι ι F) (u : ι → F) :
    (fun i => σ ((M *ᵥ u) i)) = (M.map σ) *ᵥ (fun i => σ (u i)) := by
  ext i
  simp [Matrix.mulVec, Matrix.map_apply, dotProduct, map_sum, map_mul]

private lemma rckRPdp_map_mulVec {ι F : Type} [Fintype ι] [Field F] (σ : F →+* F)
    (hσ : ∀ c, σ (σ c) = c) (M : Matrix ι ι F) (w : ι → F) :
    (M.map σ) *ᵥ w = fun i => σ ((M *ᵥ (fun j => σ (w j))) i) := by
  simpa [hσ] using (rckRPdp_sigma_mulVec σ M (fun j => σ (w j))).symm

private lemma rckRPdp_map_mulVec_eq_zero {ι F : Type} [Fintype ι] [Field F] (σ : F →+* F)
    (hσ : ∀ c, σ (σ c) = c) (M : Matrix ι ι F) (w : ι → F) :
    (M.map σ) *ᵥ w = 0 ↔ M *ᵥ (fun j => σ (w j)) = 0 := by
  rw [rckRPdp_map_mulVec σ hσ M w]
  constructor
  · intro h
    funext i
    exact σ.injective (by simpa using congrFun h i)
  · intro h
    funext i
    simp [h]

private lemma rckRPdp_B_adjoint {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) {G : Matrix ι ι F} (hG : IsUnit G.det) (M : Matrix ι ι F)
    (u v : ι → F) :
    rckRPdp_B σ G (M *ᵥ u) v = rckRPdp_B σ G u (formAdj σ G M *ᵥ v) := by
  have hGN : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hG
  have h1 : rckRPdp_B σ G (M *ᵥ u) v =
      dotProduct (fun i => σ (u i))
        (Matrix.transpose (M.map σ) *ᵥ (G *ᵥ v)) := by
    simp only [rckRPdp_B]
    rw [rckRPdp_sigma_mulVec σ M u, dotProduct_comm,
      ← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec]
  have h2 : rckRPdp_B σ G u (formAdj σ G M *ᵥ v) =
      dotProduct (fun i => σ (u i))
        (Matrix.transpose (M.map σ) *ᵥ (G *ᵥ v)) := by
    simp only [rckRPdp_B]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have hmat : G * formAdj σ G M = (M.map σ)ᵀ * G := by
      unfold formAdj
      calc G * (G⁻¹ * (M.map σ)ᵀ * G)
          = (G * G⁻¹) * ((M.map σ)ᵀ * G) := by
              rw [Matrix.mul_assoc G⁻¹ ((M.map σ)ᵀ) G,
                ← Matrix.mul_assoc G G⁻¹ ((M.map σ)ᵀ * G)]
        _ = (M.map σ)ᵀ * G := by rw [hGN, Matrix.one_mul]
    rw [hmat]
  rw [h1, h2]

private lemma rckRPdp_rank_fromBlocks_one_zero (F : Type) [Field F] (r s : ℕ) :
    (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0
      (0 : Matrix (Fin s) (Fin s) F)).rank = r := by
  classical
  have h : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0
      (0 : Matrix (Fin s) (Fin s) F)) =
      Matrix.diagonal (Sum.elim (fun _ : Fin r => (1 : F)) (fun _ : Fin s => (0 : F))) := by
    rw [← Matrix.fromBlocks_diagonal, Matrix.diagonal_one, Matrix.diagonal_zero]
  rw [h, Matrix.rank_diagonal, Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  simp

private lemma rckRPdp_rank_map_ringHom {F E : Type} [Field F] [Field E] (φ : F →+* E) {m : Type}
    [Fintype m] [DecidableEq m] (M : Matrix m m F) : (M.map φ).rank = M.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, h⟩ := Matrix.exists_rank_normal_form M
  have hVf : IsUnit (V.map φ).det := (Matrix.isUnit_iff_isUnit_det _).mp (hV.map φ.mapMatrix)
  have hUf : IsUnit (U.map φ).det := (Matrix.isUnit_iff_isUnit_det _).mp (hU.map φ.mapMatrix)
  have hE : (M.map φ).rank = ((V.map φ) * (M.map φ) * (U.map φ)).rank := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUf,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVf]
  have h1 : (V * M * U).map φ =
      ((Matrix.fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) F) 0 0
        (0 : Matrix (Fin (Fintype.card m - M.rank)) (Fin (Fintype.card m - M.rank)) F)).submatrix
          e e).map φ := by rw [h]
  simp only [Matrix.map_mul, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_zero _ (map_zero φ)] at h1
  rw [hE, h1, Matrix.rank_submatrix, rckRPdp_rank_fromBlocks_one_zero]

private lemma rckRPdp_rank_formAdj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) {G : Matrix ι ι F} (hG : IsUnit G.det) (M : Matrix ι ι F) :
    Matrix.rank (formAdj σ G M) = Matrix.rank M := by
  have hX : (G⁻¹ * Matrix.transpose (M.map σ)).rank = M.rank := by
    rw [Matrix.rank_mul_eq_right_of_isUnit_det G⁻¹ (Matrix.transpose (M.map σ))
      (Matrix.isUnit_nonsing_inv_det G hG), Matrix.rank_transpose,
      rckRPdp_rank_map_ringHom σ M]
  unfold formAdj
  rw [Matrix.rank_mul_eq_left_of_isUnit_det G (G⁻¹ * Matrix.transpose (M.map σ)) hG, hX]

private lemma rckRPdp_finrank_range {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (M : Matrix ι ι F) :
    Module.finrank F (LinearMap.range (Matrix.toLin' M)) = M.rank := by
  rw [Matrix.range_toLin', ← Matrix.rank_eq_finrank_span_cols]

private lemma rckRPdp_finrank_ker_map_sigma {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) (M : Matrix ι ι F) :
    Module.finrank F (LinearMap.ker (Matrix.toLin' (M.map σ))) =
      Module.finrank F (LinearMap.ker (Matrix.toLin' M)) := by
  have hV : Module.finrank F (ι → F) = Fintype.card ι := Module.finrank_fintype_fun_eq_card F
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (M.map σ))
  have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
  have h3 : Module.finrank F (LinearMap.range (Matrix.toLin' (M.map σ))) =
      Module.finrank F (LinearMap.range (Matrix.toLin' M)) := by
    rw [rckRPdp_finrank_range, rckRPdp_finrank_range, rckRPdp_rank_map_ringHom σ M]
  omega

private lemma rckRPdp_perp_ker_eq_orthogonal {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) (hσ : ∀ c, σ (σ c) = c) (G M : Matrix ι ι F) :
    rckRPdp_perp σ G (LinearMap.ker (Matrix.toLin' M)) =
      (Matrix.toBilin' G).orthogonal
        (LinearMap.ker (Matrix.toLin' (M.map σ))) := by
  ext v
  simp only [rckRPdp_mem_perp, LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.mem_ker,
    Matrix.toLin'_apply, Matrix.toBilin'_apply']
  constructor
  · intro hv w hw
    have hu : M *ᵥ (fun j => σ (w j)) = 0 :=
      (rckRPdp_map_mulVec_eq_zero σ hσ M w).mp hw
    have h := hv (fun j => σ (w j)) hu
    simpa [rckRPdp_B, hσ] using h
  · intro hv u hu
    have hw : (M.map σ) *ᵥ (fun j => σ (u j)) = 0 := by
      rw [rckRPdp_map_mulVec_eq_zero σ hσ M (fun j => σ (u j))]
      simpa [hσ] using hu
    have h := hv (fun j => σ (u j)) hw
    simpa [rckRPdp_B, hσ] using h

private lemma rckRPdp_finrank_perp_ker {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) (hσ : ∀ c, σ (σ c) = c) {G : Matrix ι ι F} (hG : IsUnit G.det)
    (M : Matrix ι ι F) :
    Module.finrank F (rckRPdp_perp σ G (LinearMap.ker (Matrix.toLin' M))) =
      Module.finrank F (LinearMap.range (Matrix.toLin' (formAdj σ G M))) := by
  rw [rckRPdp_perp_ker_eq_orthogonal σ hσ G M]
  rw [LinearMap.BilinForm.finrank_orthogonal
    (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr (isUnit_iff_ne_zero.mp hG))]
  rw [rckRPdp_finrank_ker_map_sigma σ M]
  rw [rckRPdp_finrank_range (formAdj σ G M), rckRPdp_rank_formAdj σ hG M]
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
  rw [rckRPdp_finrank_range M] at h
  omega

private lemma rckRPdp_range_formAdj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) (hσ : ∀ c, σ (σ c) = c) {G : Matrix ι ι F} (hG : IsUnit G.det)
    (M : Matrix ι ι F) :
    LinearMap.range (Matrix.toLin' (formAdj σ G M)) =
      rckRPdp_perp σ G (LinearMap.ker (Matrix.toLin' M)) := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro v ⟨w, rfl⟩
    rw [rckRPdp_mem_perp]
    intro u hu
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hu
    rw [Matrix.toLin'_apply, ← rckRPdp_B_adjoint σ hG M u w]
    simp [rckRPdp_B, hu]
  · rw [rckRPdp_finrank_perp_ker σ hσ hG M]

private lemma rckRPdp_ker_formAdj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) (hσ : ∀ c, σ (σ c) = c) {G : Matrix ι ι F} (hG : IsUnit G.det)
    (M : Matrix ι ι F) :
    LinearMap.ker (Matrix.toLin' (formAdj σ G M)) =
      rckRPdp_perp σ G (LinearMap.range (Matrix.toLin' M)) := by
  ext v
  constructor
  · intro hv
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv
    rw [rckRPdp_mem_perp]
    rintro _ ⟨u, rfl⟩
    rw [Matrix.toLin'_apply, rckRPdp_B_adjoint σ hG M u v]
    simp [rckRPdp_B, hv]
  · intro hv
    rw [LinearMap.mem_ker, Matrix.toLin'_apply]
    have hz : ∀ z : ι → F, z ⬝ᵥ (G *ᵥ (formAdj σ G M *ᵥ v)) = 0 := by
      intro z
      have h := hv (M *ᵥ (fun i => σ (z i))) ⟨_, rfl⟩
      rw [rckRPdp_B_adjoint σ hG M (fun i => σ (z i)) v] at h
      simpa [rckRPdp_B, hσ] using h
    have hGN : G *ᵥ (formAdj σ G M *ᵥ v) = 0 := by
      ext i
      have h := hz (Pi.single i 1)
      simpa [single_one_dotProduct] using h
    have h := congrArg (fun w => G⁻¹ *ᵥ w) hGN
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h
    have hGNinv : G⁻¹ * G * formAdj σ G M = formAdj σ G M := by
      rw [Matrix.nonsing_inv_mul G hG, Matrix.one_mul]
    simpa [hGNinv] using h

private lemma rckRPdp_comm_formAdj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) {G : Matrix ι ι F} (hG : IsUnit G.det) {e : Matrix ι ι F}
    {x : GL ι F} (hiso : Matrix.transpose ((x : Matrix ι ι F).map σ) * G *
      (x : Matrix ι ι F) = G)
    (hcomm : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F)) :
    (x : Matrix ι ι F) * formAdj σ G e = formAdj σ G e * (x : Matrix ι ι F) := by
  have hxstar : formAdj σ G (x : Matrix ι ι F) = ((x⁻¹ : GL ι F) : Matrix ι ι F) :=
    Geo.formAdj_eq_inv_of_isometry σ hG x hiso
  have h := congrArg (formAdj σ G) hcomm
  simp only [Geo.formAdj_mul σ hG, hxstar] at h
  have hxinvx : ((x⁻¹ : GL ι F) : Matrix ι ι F) * (x : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hxxinv : (x : Matrix ι ι F) * ((x⁻¹ : GL ι F) : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (x : Matrix ι ι F) * formAdj σ G e
      = ((x : Matrix ι ι F) * formAdj σ G e) * 1 := (Matrix.mul_one _).symm
    _ = ((x : Matrix ι ι F) * formAdj σ G e) *
          (((x⁻¹ : GL ι F) : Matrix ι ι F) * (x : Matrix ι ι F)) := by rw [hxinvx]
    _ = (x : Matrix ι ι F) *
          ((formAdj σ G e * ((x⁻¹ : GL ι F) : Matrix ι ι F)) * (x : Matrix ι ι F)) := by
          rw [Matrix.mul_assoc, ← Matrix.mul_assoc (formAdj σ G e)
            ((x⁻¹ : GL ι F) : Matrix ι ι F) (x : Matrix ι ι F)]
    _ = (x : Matrix ι ι F) *
          ((((x⁻¹ : GL ι F) : Matrix ι ι F) * formAdj σ G e) * (x : Matrix ι ι F)) := by
          rw [h]
    _ = formAdj σ G e * (x : Matrix ι ι F) := by
          rw [← Matrix.mul_assoc (x : Matrix ι ι F)
              (((x⁻¹ : GL ι F) : Matrix ι ι F) * formAdj σ G e) (x : Matrix ι ι F),
            ← Matrix.mul_assoc (x : Matrix ι ι F) ((x⁻¹ : GL ι F) : Matrix ι ι F)
              (formAdj σ G e), hxxinv, Matrix.one_mul]

private lemma rckRPdp_formAdj_neg {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) (G a : Matrix ι ι F) :
    formAdj σ G (-a) = -formAdj σ G a := by
  unfold formAdj
  rw [Matrix.map_neg σ (map_neg σ), Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul]

private lemma rckRPdp_formAdj_sub {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) (G a b : Matrix ι ι F) :
    formAdj σ G (a - b) = formAdj σ G a - formAdj σ G b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, Geo.formAdj_add, rckRPdp_formAdj_neg]

private lemma rckRPdp_formAdj_sub_one {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) {G : Matrix ι ι F} (hG : IsUnit G.det) {x : GL ι F}
    (hiso : Matrix.transpose ((x : Matrix ι ι F).map σ) * G * (x : Matrix ι ι F) = G) :
    formAdj σ G ((x : Matrix ι ι F) - 1) = ((x⁻¹ : GL ι F) : Matrix ι ι F) - 1 := by
  rw [rckRPdp_formAdj_sub, Geo.formAdj_eq_inv_of_isometry σ hG x hiso,
    Geo.formAdj_one σ hG]

private lemma rckRPdp_sub_one_eq_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {x e f : Matrix ι ι F} (hfix : x * (1 - (e + f)) = 1 - (e + f)) :
    x - 1 = (x - 1) * (e + f) := by
  have hx : x = x * (e + f) + (1 - (e + f)) := by
    calc x = x * 1 := (Matrix.mul_one x).symm
      _ = x * ((e + f) + (1 - (e + f))) := by rw [add_sub_cancel]
      _ = x * (e + f) + x * (1 - (e + f)) := by rw [Matrix.mul_add]
      _ = x * (e + f) + (1 - (e + f)) := by rw [hfix]
  have hxε : x * (e + f) = x - (1 - (e + f)) := (eq_sub_iff_add_eq).mpr hx.symm
  rw [Matrix.sub_mul, Matrix.one_mul, hxε, sub_sub, sub_add_cancel]

private lemma rckRPdp_ker_mul_e {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {x : GL ι F} {e : Matrix ι ι F} {U₂ : Submodule F (ι → F)}
    (hU₂ : LinearMap.ker (Matrix.toLin' ((x : Matrix ι ι F) - 1)) ⊓
        LinearMap.range (Matrix.toLin' e) = U₂) :
    LinearMap.ker (Matrix.toLin' (((x : Matrix ι ι F) - 1) * e)) =
      Submodule.comap (Matrix.toLin' e) U₂ := by
  rw [Matrix.toLin'_mul, LinearMap.ker_comp, ← hU₂]
  ext v
  constructor
  · intro hv
    rw [Submodule.mem_comap] at hv
    constructor
    · change (Matrix.toLin' ((x : Matrix ι ι F) - 1)) ((Matrix.toLin' e) v) = 0
      rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv
      rwa [Matrix.toLin'_apply]
    · exact ⟨v, rfl⟩
  · intro hv
    rw [Submodule.mem_comap] at hv
    rw [Submodule.mem_inf, LinearMap.mem_ker, Matrix.toLin'_apply] at hv
    rw [Submodule.mem_comap, LinearMap.mem_ker, Matrix.toLin'_apply]
    simpa [Matrix.mulVec_mulVec] using hv.1

private lemma rckRPdp_range_ker_add {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {M N e f : Matrix ι ι F} (hMeN : (M + N) * e = M) (hNeM : (M + N) * f = N)
    (heMN : e * (M + N) = M) (hfMN : f * (M + N) = N) :
    LinearMap.range (Matrix.toLin' (M + N)) =
        LinearMap.range (Matrix.toLin' M) ⊔ LinearMap.range (Matrix.toLin' N) ∧
    LinearMap.ker (Matrix.toLin' (M + N)) =
        LinearMap.ker (Matrix.toLin' M) ⊓ LinearMap.ker (Matrix.toLin' N) := by
  constructor
  · apply le_antisymm
    · rintro v ⟨u, rfl⟩
      rw [Matrix.toLin'_apply, Matrix.add_mulVec]
      exact Submodule.add_mem_sup ⟨u, rfl⟩ ⟨u, rfl⟩
    · apply sup_le
      · rintro v ⟨u, rfl⟩
        refine ⟨e *ᵥ u, ?_⟩
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec u (M + N) e, hMeN]
      · rintro v ⟨u, rfl⟩
        refine ⟨f *ᵥ u, ?_⟩
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec u (M + N) f, hNeM]
  · apply le_antisymm
    · intro v hv
      rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv
      rw [Submodule.mem_inf]
      constructor
      · rw [LinearMap.mem_ker, Matrix.toLin'_apply]
        have h := congrArg (fun w => e *ᵥ w) hv
        rw [Matrix.mulVec_zero] at h
        rwa [Matrix.mulVec_mulVec, heMN] at h
      · rw [LinearMap.mem_ker, Matrix.toLin'_apply]
        have h := congrArg (fun w => f *ᵥ w) hv
        rw [Matrix.mulVec_zero] at h
        rwa [Matrix.mulVec_mulVec, hfMN] at h
    · rintro v ⟨hMv, hNv⟩
      change (Matrix.toLin' (M + N)) v = 0
      have hMv' : (Matrix.toLin' M) v = 0 := hMv
      have hNv' : (Matrix.toLin' N) v = 0 := hNv
      rw [Matrix.toLin'_apply, Matrix.add_mulVec]
      have hMv'' : M *ᵥ v = 0 := by simpa [Matrix.toLin'_apply] using hMv'
      have hNv'' : N *ᵥ v = 0 := by simpa [Matrix.toLin'_apply] using hNv'
      rw [hMv'', hNv'', add_zero]

private lemma rckRPdp_flag_eq {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) (hσ : ∀ c, σ (σ c) = c) {G : Matrix ι ι F} (hG : IsUnit G.det)
    {e : Matrix ι ι F} (he : IsIdempotentElem e)
    (he₁ : e * formAdj σ G e = 0) (he₂ : formAdj σ G e * e = 0)
    {x : GL ι F}
    (hiso : Matrix.transpose ((x : Matrix ι ι F).map σ) * G * (x : Matrix ι ι F) = G)
    (hcomm : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F))
    (hfix : (x : Matrix ι ι F) * (1 - (e + formAdj σ G e)) =
      1 - (e + formAdj σ G e))
    (hinv : x * x = 1) {U₁ U₂ : Submodule F (ι → F)} (hU : U₁ ≤ U₂)
    (hU₁ : LinearMap.range (Matrix.toLin' (((x : Matrix ι ι F) - 1) * e)) = U₁)
    (hU₂ : LinearMap.ker (Matrix.toLin' ((x : Matrix ι ι F) - 1)) ⊓
      LinearMap.range (Matrix.toLin' e) = U₂) :
    LinearMap.range (Matrix.toLin' ((x : Matrix ι ι F) - 1)) =
        U₁ ⊔ rckRPdp_perp σ G (Submodule.comap (Matrix.toLin' e) U₂) ∧
    LinearMap.ker (Matrix.toLin' ((x : Matrix ι ι F) - 1)) =
        Submodule.comap (Matrix.toLin' e) U₂ ⊓ rckRPdp_perp σ G U₁ ∧
    U₁ ⊔ rckRPdp_perp σ G (Submodule.comap (Matrix.toLin' e) U₂) ≤
      Submodule.comap (Matrix.toLin' e) U₂ ⊓ rckRPdp_perp σ G U₁ := by
  let f := formAdj σ G e
  let M := ((x : Matrix ι ι F) - 1) * e
  let N := ((x : Matrix ι ι F) - 1) * f
  have hf : IsIdempotentElem f := by
    rw [isIdempotentElem_iff] at he ⊢
    dsimp only [f]
    rw [← Geo.formAdj_mul σ hG, he]
  have hxf : (x : Matrix ι ι F) * f = f * (x : Matrix ι ι F) :=
    rckRPdp_comm_formAdj σ hG hiso hcomm
  have hxinv : ((x⁻¹ : GL ι F) : Matrix ι ι F) = (x : Matrix ι ι F) := by
    have h := eq_inv_of_mul_eq_one_right hinv
    rw [← h]
  have hNadj : N = formAdj σ G M := by
    have hxsub := rckRPdp_formAdj_sub_one σ hG hiso
    have hsubf : ((x : Matrix ι ι F) - 1) * f = f * ((x : Matrix ι ι F) - 1) := by
      calc ((x : Matrix ι ι F) - 1) * f = (x : Matrix ι ι F) * f - 1 * f := by
            rw [Matrix.sub_mul]
        _ = (x : Matrix ι ι F) * f - f := by rw [Matrix.one_mul]
        _ = f * (x : Matrix ι ι F) - f := by rw [hxf]
        _ = f * (x : Matrix ι ι F) - f * 1 := by rw [Matrix.mul_one]
        _ = f * ((x : Matrix ι ι F) - 1) := by rw [Matrix.mul_sub]
    calc N = ((x : Matrix ι ι F) - 1) * f := rfl
      _ = f * ((x : Matrix ι ι F) - 1) := hsubf
      _ = formAdj σ G e * formAdj σ G ((x : Matrix ι ι F) - 1) := by
            rw [hxsub, hxinv]
      _ = formAdj σ G (((x : Matrix ι ι F) - 1) * e) := by
            rw [← Geo.formAdj_mul σ hG]
      _ = formAdj σ G M := rfl
  have h_e_sub : e * ((x : Matrix ι ι F) - 1) = ((x : Matrix ι ι F) - 1) * e := by
    calc e * ((x : Matrix ι ι F) - 1) = e * (x : Matrix ι ι F) - e * 1 := by
          rw [Matrix.mul_sub]
      _ = e * (x : Matrix ι ι F) - e := by rw [Matrix.mul_one]
      _ = (x : Matrix ι ι F) * e - e := by rw [← hcomm]
      _ = (x : Matrix ι ι F) * e - 1 * e := by rw [Matrix.one_mul]
      _ = ((x : Matrix ι ι F) - 1) * e := by rw [Matrix.sub_mul]
  have h_f_sub : f * ((x : Matrix ι ι F) - 1) = ((x : Matrix ι ι F) - 1) * f := by
    calc f * ((x : Matrix ι ι F) - 1) = f * (x : Matrix ι ι F) - f * 1 := by
          rw [Matrix.mul_sub]
      _ = f * (x : Matrix ι ι F) - f := by rw [Matrix.mul_one]
      _ = (x : Matrix ι ι F) * f - f := by rw [← hxf]
      _ = (x : Matrix ι ι F) * f - 1 * f := by rw [Matrix.one_mul]
      _ = ((x : Matrix ι ι F) - 1) * f := by rw [Matrix.sub_mul]
  have heM : e * M = M := by
    dsimp only [M]
    rw [← Matrix.mul_assoc, h_e_sub, Matrix.mul_assoc, he.eq]
  have hfN : f * N = N := by
    dsimp only [N]
    rw [← Matrix.mul_assoc, h_f_sub, Matrix.mul_assoc, hf.eq]
  have hMf : M * f = 0 := by
    dsimp only [M]
    rw [Matrix.mul_assoc, he₁, Matrix.mul_zero]
  have hNe : N * e = 0 := by
    dsimp only [N]
    rw [Matrix.mul_assoc, he₂, Matrix.mul_zero]
  have hfM : f * M = 0 := by
    dsimp only [M]
    rw [← Matrix.mul_assoc, h_f_sub, Matrix.mul_assoc, he₂, Matrix.mul_zero]
  have heN : e * N = 0 := by
    dsimp only [N]
    rw [← Matrix.mul_assoc, h_e_sub, Matrix.mul_assoc, he₁, Matrix.mul_zero]
  have hMe : M * e = M := by
    dsimp only [M]
    rw [Matrix.mul_assoc, he.eq]
  have hNf : N * f = N := by
    dsimp only [N]
    rw [Matrix.mul_assoc, hf.eq]
  have hMeN : (M + N) * e = M := by rw [Matrix.add_mul, hMe, hNe, add_zero]
  have hNeM : (M + N) * f = N := by rw [Matrix.add_mul, hMf, hNf, zero_add]
  have heMN : e * (M + N) = M := by rw [Matrix.mul_add, heM, heN, add_zero]
  have hfMN : f * (M + N) = N := by rw [Matrix.mul_add, hfM, hfN, zero_add]
  have hMN : (x : Matrix ι ι F) - 1 = M + N := by
    rw [rckRPdp_sub_one_eq_mul hfix, Matrix.mul_add]
  have hdecomp := rckRPdp_range_ker_add hMeN hNeM heMN hfMN
  have hMker : LinearMap.ker (Matrix.toLin' M) = Submodule.comap (Matrix.toLin' e) U₂ :=
    rckRPdp_ker_mul_e hU₂
  have hNrange : LinearMap.range (Matrix.toLin' N) =
      rckRPdp_perp σ G (LinearMap.ker (Matrix.toLin' M)) := by
    rw [hNadj]
    exact rckRPdp_range_formAdj σ hσ hG M
  have hNker : LinearMap.ker (Matrix.toLin' N) =
      rckRPdp_perp σ G (LinearMap.range (Matrix.toLin' M)) := by
    rw [hNadj]
    exact rckRPdp_ker_formAdj σ hσ hG M
  have hU₁Q : U₁ ≤ Submodule.comap (Matrix.toLin' e) U₂ := by
    intro v hv
    rw [Submodule.mem_comap]
    have hvM : v ∈ LinearMap.range (Matrix.toLin' M) := by rw [hU₁]; exact hv
    obtain ⟨a, rfl⟩ := hvM
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec a e M, heM]
    exact hU (by
      dsimp only [M]
      rw [← hU₁]
      exact ⟨a, rfl⟩)
  have hNM : N * M = 0 := by
    calc N * M = (((x : Matrix ι ι F) - 1) * (f * ((x : Matrix ι ι F) - 1))) * e := by
          dsimp only [N, M]
          rw [← Matrix.mul_assoc (((x : Matrix ι ι F) - 1) * f)
              ((x : Matrix ι ι F) - 1) e,
            Matrix.mul_assoc ((x : Matrix ι ι F) - 1) f ((x : Matrix ι ι F) - 1)]
      _ = (((x : Matrix ι ι F) - 1) * (((x : Matrix ι ι F) - 1) * f)) * e := by
          rw [h_f_sub]
      _ = ((((x : Matrix ι ι F) - 1) * ((x : Matrix ι ι F) - 1)) * f) * e := by
          rw [← Matrix.mul_assoc ((x : Matrix ι ι F) - 1) ((x : Matrix ι ι F) - 1) f]
      _ = (((x : Matrix ι ι F) - 1) * ((x : Matrix ι ι F) - 1)) * (f * e) := by
          rw [← Matrix.mul_assoc (((x : Matrix ι ι F) - 1) *
            ((x : Matrix ι ι F) - 1)) f e]
      _ = 0 := by rw [he₂, Matrix.mul_zero]
  have hU₁perp : U₁ ≤ rckRPdp_perp σ G U₁ := by
    intro v hv
    rw [rckRPdp_mem_perp]
    intro u hu
    have hvM : v ∈ LinearMap.range (Matrix.toLin' M) := by rw [hU₁]; exact hv
    have huM : u ∈ LinearMap.range (Matrix.toLin' M) := by rw [hU₁]; exact hu
    obtain ⟨a, rfl⟩ := huM
    obtain ⟨b, rfl⟩ := hvM
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, rckRPdp_B_adjoint σ hG M a (M *ᵥ b),
      ← hNadj, Matrix.mulVec_mulVec b N M, hNM, Matrix.zero_mulVec]
    simp [rckRPdp_B]
  have hP_Q : rckRPdp_perp σ G (Submodule.comap (Matrix.toLin' e) U₂) ≤
      Submodule.comap (Matrix.toLin' e) U₂ := by
    intro v hv
    rw [Submodule.mem_comap]
    have hvN : v ∈ LinearMap.range (Matrix.toLin' N) := by rw [hNrange, hMker]; exact hv
    obtain ⟨b, rfl⟩ := hvN
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec b e N, heN,
      Matrix.zero_mulVec]
    exact Submodule.zero_mem U₂
  have hP_perp : rckRPdp_perp σ G (Submodule.comap (Matrix.toLin' e) U₂) ≤
      rckRPdp_perp σ G U₁ := by
    intro v hv
    rw [rckRPdp_mem_perp] at hv ⊢
    intro u hu
    exact hv u (hU₁Q hu)
  refine ⟨?_, ?_, ?_⟩
  · rw [hMN, hdecomp.1, hU₁, hNrange, hMker]
  · rw [hMN, hdecomp.2, hMker, hNker, hU₁]
  · exact sup_le (le_inf hU₁Q hU₁perp) (le_inf hP_Q hP_perp)
theorem glGeoFlag_none_of_dualPair {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    (σ : F →+* F) (hσ : ∀ c, σ (σ c) = c) {G : Matrix ι ι F} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map σ) = G) {e : Matrix ι ι F} (he : IsIdempotentElem e)
    (he₁ : e * formAdj σ G e = 0) (he₂ : formAdj σ G e * e = 0) {R : Subgroup (GL ι F)}
    (hiso : ∀ x ∈ R, Matrix.transpose ((x : Matrix ι ι F).map σ) * G * (x : Matrix ι ι F) = G)
    (hcomm : ∀ x ∈ R, (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F))
    (hfix : ∀ x ∈ R, (x : Matrix ι ι F) * (1 - (e + formAdj σ G e)) = 1 - (e + formAdj σ G e))
    (hinv : ∀ x ∈ R, x * x = 1) {U₁ U₂ : Submodule F (ι → F)} (hU : U₁ ≤ U₂)
    (hflag : ∀ x ∈ R, x ≠ 1 →
      LinearMap.range (Matrix.toLin' (((x : Matrix ι ι F) - 1) * e)) = U₁ ∧
      LinearMap.ker (Matrix.toLin' ((x : Matrix ι ι F) - 1)) ⊓
        LinearMap.range (Matrix.toLin' e) = U₂) :
    GLGeoFlag none R := by
  classical
  by_cases hex : ∃ x ∈ R, x ≠ 1
  · obtain ⟨x₀, hx₀R, hx₀1⟩ := hex
    obtain ⟨hU₁, hU₂⟩ := hflag x₀ hx₀R hx₀1
    obtain ⟨hxrange, hxker, hxWH⟩ :=
      rckRPdp_flag_eq σ hσ hG he he₁ he₂ (hiso x₀ hx₀R) (hcomm x₀ hx₀R)
        (hfix x₀ hx₀R) (hinv x₀ hx₀R) hU hU₁ hU₂
    refine ⟨LinearMap.range (Matrix.toLin' ((x₀ : Matrix ι ι F) - 1)),
      LinearMap.ker (Matrix.toLin' ((x₀ : Matrix ι ι F) - 1)), ?_, ?_, ?_⟩
    · rw [hxrange, hxker]
      exact hxWH
    · intro x hx hx1
      obtain ⟨hU₁x, hU₂x⟩ := hflag x hx hx1
      obtain ⟨hxrange', hxker', -⟩ :=
        rckRPdp_flag_eq σ hσ hG he he₁ he₂ (hiso x hx) (hcomm x hx)
          (hfix x hx) (hinv x hx) hU hU₁x hU₂x
      exact ⟨hxrange'.trans hxrange.symm, hxker'.trans hxker.symm⟩
    · intro b hb
      exact ((Option.not_mem_none b) hb).elim
  · refine ⟨⊥, ⊥, le_refl _, ?_, ?_⟩
    · intro x hx hx1
      exact absurd ⟨x, hx, hx1⟩ hex
    · intro b hb
      exact ((Option.not_mem_none b) hb).elim

private lemma rckRPdp_Bstd_skew {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G : Matrix ι ι F} (halt : ∀ v : ι → F, v ⬝ᵥ (G *ᵥ v) = 0) (u v : ι → F) :
    u ⬝ᵥ (G *ᵥ v) = -(v ⬝ᵥ (G *ᵥ u)) := by
  have h := halt (u + v)
  have hu := halt u
  have hv := halt v
  have h' : u ⬝ᵥ (G *ᵥ v) + v ⬝ᵥ (G *ᵥ u) = 0 := by
    rw [add_comm]
    simpa [Matrix.mulVec_add, dotProduct_add, add_dotProduct, hu, hv] using h
  exact eq_neg_of_add_eq_zero_left h'

private lemma rckRPdp_Bstd_isometry {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G : Matrix ι ι F} {x : GL ι F}
    (hiso : Matrix.transpose (x : Matrix ι ι F) * G * (x : Matrix ι ι F) = G)
    (u v : ι → F) :
    (x : Matrix ι ι F) *ᵥ u ⬝ᵥ (G *ᵥ ((x : Matrix ι ι F) *ᵥ v)) =
      u ⬝ᵥ (G *ᵥ v) := by
  calc (x : Matrix ι ι F) *ᵥ u ⬝ᵥ (G *ᵥ ((x : Matrix ι ι F) *ᵥ v))
      = u ⬝ᵥ (Matrix.transpose (x : Matrix ι ι F) *ᵥ
          (G *ᵥ ((x : Matrix ι ι F) *ᵥ v))) := by
          rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
    _ = u ⬝ᵥ (G *ᵥ v) := by
          rw [Matrix.mulVec_mulVec ((x : Matrix ι ι F) *ᵥ v)
              (Matrix.transpose (x : Matrix ι ι F)) G,
            Matrix.mulVec_mulVec v (Matrix.transpose (x : Matrix ι ι F) * G)
              (x : Matrix ι ι F), hiso]

private lemma rckRPdp_Bstd_formAdj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G : Matrix ι ι F} (hG : IsUnit G.det) (M : Matrix ι ι F) (u v : ι → F) :
    M *ᵥ u ⬝ᵥ (G *ᵥ v) =
      u ⬝ᵥ (G *ᵥ (formAdj (RingHom.id F) G M *ᵥ v)) := by
  simpa [rckRPdp_B, Matrix.map_id] using
    (rckRPdp_B_adjoint (RingHom.id F) hG M u v)

private lemma rckRPdp_q_cross {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G : Matrix ι ι F} (halt : ∀ v : ι → F, v ⬝ᵥ (G *ᵥ v) = 0) {x : GL ι F}
    (hiso : Matrix.transpose (x : Matrix ι ι F) * G * (x : Matrix ι ι F) = G)
    (hinv : x * x = 1) (m m' : ι → F) :
    m ⬝ᵥ (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ m')) +
      m' ⬝ᵥ (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ m)) = 0 := by
  have hxx : (x : Matrix ι ι F) * (x : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, hinv, Units.val_one]
  have hxxm : ∀ w : ι → F,
      (x : Matrix ι ι F) *ᵥ ((x : Matrix ι ι F) *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec w (x : Matrix ι ι F) (x : Matrix ι ι F), hxx,
      Matrix.one_mulVec]
  have hsub : ∀ u w : ι → F,
      u ⬝ᵥ (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ w)) =
        u ⬝ᵥ ((G * (x : Matrix ι ι F)) *ᵥ w) - u ⬝ᵥ (G *ᵥ w) := by
    intro u w
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, dotProduct_sub,
      Matrix.mulVec_mulVec w G (x : Matrix ι ι F)]
  have h1 : m' ⬝ᵥ ((G * (x : Matrix ι ι F)) *ᵥ m) =
      (x : Matrix ι ι F) *ᵥ m' ⬝ᵥ (G *ᵥ m) := by
    rw [← Matrix.mulVec_mulVec m G (x : Matrix ι ι F),
      ← rckRPdp_Bstd_isometry hiso m' ((x : Matrix ι ι F) *ᵥ m), hxxm m]
  have h2 : m ⬝ᵥ ((G * (x : Matrix ι ι F)) *ᵥ m') =
      (x : Matrix ι ι F) *ᵥ m ⬝ᵥ (G *ᵥ m') := by
    rw [← Matrix.mulVec_mulVec m' G (x : Matrix ι ι F),
      ← rckRPdp_Bstd_isometry hiso m ((x : Matrix ι ι F) *ᵥ m'), hxxm m']
  have h3 : m' ⬝ᵥ (G *ᵥ m) = -(m ⬝ᵥ (G *ᵥ m')) :=
    rckRPdp_Bstd_skew halt m' m
  have h4 : (x : Matrix ι ι F) *ᵥ m' ⬝ᵥ (G *ᵥ m) =
      -((x : Matrix ι ι F) *ᵥ m ⬝ᵥ (G *ᵥ m')) := by
    rw [rckRPdp_Bstd_skew halt ((x : Matrix ι ι F) *ᵥ m') m,
      Matrix.mulVec_mulVec m' G (x : Matrix ι ι F), h2]
  rw [hsub, hsub, h1, h2, h3, h4]
  simp

private lemma rckRPdp_q_add {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G : Matrix ι ι F} (halt : ∀ v : ι → F, v ⬝ᵥ (G *ᵥ v) = 0) {x : GL ι F}
    (hiso : Matrix.transpose (x : Matrix ι ι F) * G * (x : Matrix ι ι F) = G)
    (hinv : x * x = 1) (m m' : ι → F) :
    (m + m') ⬝ᵥ (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ (m + m'))) =
      m ⬝ᵥ (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ m)) +
      m' ⬝ᵥ (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ m')) := by
  have hcross := rckRPdp_q_cross halt hiso hinv m m'
  calc (m + m') ⬝ᵥ (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ (m + m')))
      = (m + m') ⬝ᵥ (G *ᵥ ((((x : Matrix ι ι F) - 1) *ᵥ m) +
          (((x : Matrix ι ι F) - 1) *ᵥ m'))) := by rw [Matrix.mulVec_add]
    _ = (m + m') ⬝ᵥ (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ m) +
          G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ m')) := by rw [Matrix.mulVec_add]
    _ = (m ⬝ᵥ (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ m)) +
          m ⬝ᵥ (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ m'))) +
          (m' ⬝ᵥ (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ m)) +
          m' ⬝ᵥ (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ m'))) := by
          rw [dotProduct_add, add_dotProduct, add_dotProduct]
          abel
    _ = m ⬝ᵥ (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ m)) +
          m' ⬝ᵥ (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ m')) := by
          linear_combination hcross

private lemma rckRPdp_q_e_f_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G : Matrix ι ι F} (hG : IsUnit G.det) {e : Matrix ι ι F}
    (he₁ : e * formAdj (RingHom.id F) G e = 0)
    (he₂ : formAdj (RingHom.id F) G e * e = 0) {x : GL ι F}
    (hiso : Matrix.transpose (x : Matrix ι ι F) * G * (x : Matrix ι ι F) = G)
    (hcomm : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F)) :
    (∀ a : ι → F,
      (e *ᵥ a) ⬝ᵥ (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ (e *ᵥ a))) = 0) ∧
    (∀ a : ι → F,
      (formAdj (RingHom.id F) G e *ᵥ a) ⬝ᵥ
        (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ
          (formAdj (RingHom.id F) G e *ᵥ a))) = 0) := by
  let f := formAdj (RingHom.id F) G e
  have hcommf : (x : Matrix ι ι F) * f = f * (x : Matrix ι ι F) :=
    rckRPdp_comm_formAdj (RingHom.id F) hG hiso hcomm
  have hsube : ((x : Matrix ι ι F) - 1) * e = e * ((x : Matrix ι ι F) - 1) := by
    calc ((x : Matrix ι ι F) - 1) * e = (x : Matrix ι ι F) * e - 1 * e := by
          rw [Matrix.sub_mul]
      _ = (x : Matrix ι ι F) * e - e := by rw [Matrix.one_mul]
      _ = e * (x : Matrix ι ι F) - e := by rw [hcomm]
      _ = e * (x : Matrix ι ι F) - e * 1 := by rw [Matrix.mul_one]
      _ = e * ((x : Matrix ι ι F) - 1) := by rw [Matrix.mul_sub]
  have hsubf : ((x : Matrix ι ι F) - 1) * f = f * ((x : Matrix ι ι F) - 1) := by
    calc ((x : Matrix ι ι F) - 1) * f = (x : Matrix ι ι F) * f - 1 * f := by
          rw [Matrix.sub_mul]
      _ = (x : Matrix ι ι F) * f - f := by rw [Matrix.one_mul]
      _ = f * (x : Matrix ι ι F) - f := by rw [hcommf]
      _ = f * (x : Matrix ι ι F) - f * 1 := by rw [Matrix.mul_one]
      _ = f * ((x : Matrix ι ι F) - 1) := by rw [Matrix.mul_sub]
  constructor
  · intro a
    rw [Matrix.mulVec_mulVec a ((x : Matrix ι ι F) - 1) e, hsube,
      ← Matrix.mulVec_mulVec a e ((x : Matrix ι ι F) - 1),
      rckRPdp_Bstd_formAdj hG e a (e *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ a)),
      Matrix.mulVec_mulVec (((x : Matrix ι ι F) - 1) *ᵥ a) f e, he₂,
      Matrix.zero_mulVec, Matrix.mulVec_zero]
    simp [Matrix.toBilin'_apply']
  · intro a
    change (f *ᵥ a) ⬝ᵥ (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ (f *ᵥ a))) = 0
    rw [Matrix.mulVec_mulVec a ((x : Matrix ι ι F) - 1) f, hsubf,
      ← Matrix.mulVec_mulVec a f ((x : Matrix ι ι F) - 1),
      ← rckRPdp_Bstd_formAdj hG e (f *ᵥ a) (((x : Matrix ι ι F) - 1) *ᵥ a),
      Matrix.mulVec_mulVec a e f, he₁, Matrix.zero_mulVec, zero_dotProduct]

private lemma rckRPdp_q_c_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G : Matrix ι ι F} {e : Matrix ι ι F} {x : GL ι F}
    (hfix : (x : Matrix ι ι F) * (1 - (e + formAdj (RingHom.id F) G e)) =
      1 - (e + formAdj (RingHom.id F) G e)) :
    ∀ a : ι → F,
      ((1 - (e + formAdj (RingHom.id F) G e)) *ᵥ a) ⬝ᵥ
        (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ
          ((1 - (e + formAdj (RingHom.id F) G e)) *ᵥ a))) = 0 := by
  intro a
  let f := formAdj (RingHom.id F) G e
  change ((1 - (e + f)) *ᵥ a) ⬝ᵥ
    (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ ((1 - (e + f)) *ᵥ a))) = 0
  have hfix' : ((x : Matrix ι ι F) - 1) * (1 - (e + f)) = 0 := by
    calc ((x : Matrix ι ι F) - 1) * (1 - (e + f)) =
          (x : Matrix ι ι F) * (1 - (e + f)) - 1 * (1 - (e + f)) := by
            rw [Matrix.sub_mul]
      _ = (1 - (e + f)) - (1 - (e + f)) := by rw [hfix, Matrix.one_mul]
      _ = 0 := sub_self _
  rw [Matrix.mulVec_mulVec a ((x : Matrix ι ι F) - 1) (1 - (e + f)), hfix',
    Matrix.zero_mulVec, Matrix.mulVec_zero, dotProduct_zero]

theorem dotProduct_mulVec_sub_one_eq_zero_of_dualPair {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] {G : Matrix ι ι F} (hG : IsUnit G.det) (halt : ∀ v : ι → F, v ⬝ᵥ (G *ᵥ v) = 0)
    {e : Matrix ι ι F} (he : IsIdempotentElem e) (he₁ : e * formAdj (RingHom.id F) G e = 0)
    (he₂ : formAdj (RingHom.id F) G e * e = 0) {x : GL ι F}
    (hiso : Matrix.transpose (x : Matrix ι ι F) * G * (x : Matrix ι ι F) = G)
    (hcomm : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F))
    (hfix : (x : Matrix ι ι F) * (1 - (e + formAdj (RingHom.id F) G e)) =
      1 - (e + formAdj (RingHom.id F) G e))
    (hinv : x * x = 1) (m : ι → F) :
    m ⬝ᵥ (G *ᵥ (((x : Matrix ι ι F) - 1) *ᵥ m)) = 0 := by
  obtain ⟨hq_e, hq_f⟩ := rckRPdp_q_e_f_zero hG he₁ he₂ hiso hcomm
  have hq_c := rckRPdp_q_c_zero (G := G) (e := e) (x := x) hfix
  have hm : e *ᵥ m + formAdj (RingHom.id F) G e *ᵥ m +
      (1 - (e + formAdj (RingHom.id F) G e)) *ᵥ m = m := by
    rw [← Matrix.add_mulVec, ← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  rw [← hm]
  rw [rckRPdp_q_add halt hiso hinv
      (e *ᵥ m + formAdj (RingHom.id F) G e *ᵥ m)
      ((1 - (e + formAdj (RingHom.id F) G e)) *ᵥ m),
    rckRPdp_q_add halt hiso hinv (e *ᵥ m) (formAdj (RingHom.id F) G e *ᵥ m)]
  rw [hq_e m, hq_f m, hq_c m]
  ring

private theorem rckRPdp_J_transpose {F : Type} [Field F] [CharP F 2] (n : ℕ) :
    (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).transpose =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.transpose, Matrix.one_apply, CharTwo.neg_eq, eq_comm]

private theorem rckRPdp_J_mul_self {F : Type} [Field F] [CharP F 2] (n : ℕ) :
    (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * Matrix.fromBlocks 0 1 (-1) 0 = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type,
      CharTwo.neg_eq]

private theorem rckRPdp_J_isUnit_det {F : Type} [Field F] [CharP F 2] (n : ℕ) :
    IsUnit (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).det :=
  Matrix.isUnit_det_of_right_inverse (rckRPdp_J_mul_self n)

private theorem rckRPdp_J_mulVec_inl {F : Type} [Field F] (n : ℕ)
    (x : Fin n ⊕ Fin n → F) (i : Fin n) :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec x
      (Sum.inl i) = x (Sum.inr i) := by
  simp [Matrix.fromBlocks, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

private theorem rckRPdp_J_mulVec_inr {F : Type} [Field F] (n : ℕ)
    (x : Fin n ⊕ Fin n → F) (i : Fin n) :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec x
      (Sum.inr i) = -x (Sum.inl i) := by
  simp [Matrix.fromBlocks, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

private theorem rckRPdp_J_alt {F : Type} [Field F] (n : ℕ) (x : Fin n ⊕ Fin n → F) :
    x ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).mulVec x = 0 := by
  have h1 := rckRPdp_J_mulVec_inl n x
  have h2 := rckRPdp_J_mulVec_inr n x
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [h1, h2, mul_neg, Finset.sum_neg_distrib]
  rw [Finset.sum_congr rfl (fun i _ => mul_comm (x (Sum.inl i)) (x (Sum.inr i)))]
  simp
theorem glGeoFlag_spForm_of_dualPair {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (he : IsIdempotentElem e)
    (he₁ : e * formAdj (RingHom.id F)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) e = 0)
    (he₂ : formAdj (RingHom.id F)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) e * e = 0)
    {R : Subgroup (GL (Fin n ⊕ Fin n) F)} (hRSp : ∀ x ∈ R, x ∈ CFSG.Open.StatedSp n F)
    (hcomm : ∀ x ∈ R, (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * e =
      e * (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))
    (hfix : ∀ x ∈ R, (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (1 - (e + formAdj (RingHom.id F)
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) e)) =
      1 - (e + formAdj (RingHom.id F)
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) e))
    (hinv : ∀ x ∈ R, x * x = 1) {U₁ U₂ : Submodule F ((Fin n ⊕ Fin n) → F)} (hU : U₁ ≤ U₂)
    (hflag : ∀ x ∈ R, x ≠ 1 →
      LinearMap.range (Matrix.toLin'
        (((x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) - 1) * e)) = U₁ ∧
      LinearMap.ker (Matrix.toLin' ((x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) - 1)) ⊓
        LinearMap.range (Matrix.toLin' e) = U₂) :
    GLGeoFlag (spForm n F) R := by
  let J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := Matrix.fromBlocks 0 1 (-1) 0
  have hJdet : IsUnit J.det := rckRPdp_J_isUnit_det n
  have hJtrans : Matrix.transpose (J.map (RingHom.id F)) = J := by
    simpa [J, Matrix.map_id] using rckRPdp_J_transpose n
  have hJalt : ∀ v : (Fin n ⊕ Fin n) → F, v ⬝ᵥ (J *ᵥ v) = 0 :=
    fun v => rckRPdp_J_alt n v
  have hiso : ∀ x ∈ R, Matrix.transpose ((x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map
      (RingHom.id F)) * J * (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = J := by
    intro x hx
    have h := CFSG.Open.StatedAPI.mem_statedSp_iff.mp (hRSp x hx)
    simpa [J, Matrix.map_id] using h
  obtain ⟨W, H, hWH, hflagW, -⟩ :=
    glGeoFlag_none_of_dualPair (σ := RingHom.id F) (hσ := fun c => rfl) hJdet hJtrans
      he he₁ he₂ hiso hcomm hfix hinv hU hflag
  refine ⟨W, H, hWH, hflagW, ?_⟩
  intro b hb
  simp only [spForm, Option.mem_some_iff] at hb
  subst b
  left
  intro x hx m
  have hxiso : Matrix.transpose (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * J *
      (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = J := by
    simpa [Matrix.map_id] using hiso x hx
  exact dotProduct_mulVec_sub_one_eq_zero_of_dualPair hJdet hJalt he he₁ he₂ hxiso
    (hcomm x hx) (hfix x hx) (hinv x hx) m

theorem glGeoFlag_polar_of_dualPair {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] {Q : QuadraticForm F (ι → F)}
    (hQ : IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det)
    {e : Matrix ι ι F} (he : IsIdempotentElem e)
    (he₁ : e * formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) e = 0)
    (he₂ : formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) e * e = 0)
    {R : Subgroup (GL ι F)}
    (hiso : ∀ x ∈ R, ∀ m m' : ι → F, QuadraticMap.polar Q ((x : Matrix ι ι F) *ᵥ m)
      ((x : Matrix ι ι F) *ᵥ m') = QuadraticMap.polar Q m m')
    (hcomm : ∀ x ∈ R, (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F))
    (hfix : ∀ x ∈ R, (x : Matrix ι ι F) *
      (1 - (e + formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) e)) =
      1 - (e + formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) e))
    (hinv : ∀ x ∈ R, x * x = 1) {U₁ U₂ : Submodule F (ι → F)} (hU : U₁ ≤ U₂)
    (hflag : ∀ x ∈ R, x ≠ 1 →
      LinearMap.range (Matrix.toLin' (((x : Matrix ι ι F) - 1) * e)) = U₁ ∧
      LinearMap.ker (Matrix.toLin' ((x : Matrix ι ι F) - 1)) ⊓
        LinearMap.range (Matrix.toLin' e) = U₂) :
    GLGeoFlag (some (QuadraticMap.polar Q)) R := by
  obtain ⟨G, hGdef⟩ : ∃ G, LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) = G := ⟨_, rfl⟩
  rw [hGdef] at hQ he₁ he₂ hfix
  have hGQ : ∀ v w : ι → F, v ⬝ᵥ (G *ᵥ w) = QuadraticMap.polar Q v w := fun v w => by
    rw [← Matrix.toLinearMap₂'_apply', ← hGdef, Matrix.toLinearMap₂'_toMatrix',
      QuadraticMap.polarBilin_apply_apply]
  have hGalt : ∀ v : ι → F, v ⬝ᵥ (G *ᵥ v) = 0 := fun v => by
    rw [hGQ, QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hGsymm : Matrix.transpose (G.map (RingHom.id F)) = G := by
    ext i k
    rw [← hGdef]
    simp only [Matrix.transpose_apply, Matrix.map_apply, RingHom.id_apply,
      LinearMap.toMatrix₂'_apply, QuadraticMap.polarBilin_apply_apply]
    exact QuadraticMap.polar_comm _ _ _
  have hisoG : ∀ x ∈ R, Matrix.transpose ((x : Matrix ι ι F).map (RingHom.id F)) * G *
      (x : Matrix ι ι F) = G := by
    intro x hx
    have hB : (QuadraticMap.polarBilin Q).compl₁₂ (Matrix.toLin' (x : Matrix ι ι F))
        (Matrix.toLin' (x : Matrix ι ι F)) = QuadraticMap.polarBilin Q :=
      LinearMap.ext₂ fun v w => by
        simp only [LinearMap.compl₁₂_apply, Matrix.toLin'_apply,
          QuadraticMap.polarBilin_apply_apply]
        exact hiso x hx v w
    have h := LinearMap.toMatrix₂'_compl₁₂ (QuadraticMap.polarBilin Q)
      (Matrix.toLin' (x : Matrix ι ι F)) (Matrix.toLin' (x : Matrix ι ι F))
    rw [hB, LinearMap.toMatrix'_toLin', hGdef] at h
    simpa [Matrix.map_id] using h.symm
  obtain ⟨W, H, hWH, hflagW, -⟩ :=
    glGeoFlag_none_of_dualPair (σ := RingHom.id F) (hσ := fun c => rfl) hQ hGsymm
      he he₁ he₂ hisoG hcomm hfix hinv hU hflag
  refine ⟨W, H, hWH, hflagW, ?_⟩
  intro b hb
  simp only [Option.mem_some_iff] at hb
  subst b
  left
  intro x hx m
  have hxiso : Matrix.transpose (x : Matrix ι ι F) * G * (x : Matrix ι ι F) = G := by
    simpa [Matrix.map_id] using hisoG x hx
  rw [← hGQ]
  exact dotProduct_mulVec_sub_one_eq_zero_of_dualPair hQ hGalt he he₁ he₂ hxiso
    (hcomm x hx) (hfix x hx) (hinv x hx) m

end CFSG.StandardType.RCKRP
