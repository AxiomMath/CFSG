module

public import CFSG.LocalAnalysis.StandardType.PhanESLMatrix

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
open scoped MatrixGroups Matrix

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {w₀ : (coxeterMatrix D.isFiniteType).Group}
  {F : FrobData D n H w₀} {n₀ : K} (L : StdLevi F n₀)

namespace StdLevi

theorem stdTau_ε (i : Fin D.rank) (A : SL(2, L.Fld)) :
    stdTau F n₀ (L.ε i A) = L.ε i (slSigma L.θ 2 A) := by
  have h : (stdTau F n₀).comp (L.ε i) = (L.ε i).comp (slSigma L.θ 2) := by
    apply sl2_hom_ext
    · intro c
      simp only [MonoidHom.coe_comp, Function.comp_apply]
      rw [stdTau_apply, L.phi_upper, L.conj_upper, slSigma_sl2Upper]
    · intro c
      simp only [MonoidHom.coe_comp, Function.comp_apply]
      rw [stdTau_apply, L.phi_lower, L.conj_lower, slSigma_sl2Lower]
  exact DFunLike.congr_fun h A

theorem ε_mem_stdFix_iff (i : Fin D.rank) (A : SL(2, L.Fld)) :
    L.ε i A ∈ stdFix F n₀ ↔ A ∈ slSU L.θ 2 := by
  rw [mem_stdFix_iff, ← stdTau_apply, L.stdTau_ε, (L.ε_inj i).eq_iff, mem_slSU_iff]

theorem stdTau_ε₂ {i j : Fin D.rank} (hij : i < j) (h3 : coxeterMatrix D.isFiniteType i j = 3)
    (A : SL(3, L.Fld)) : stdTau F n₀ (L.ε₂ i j A) = L.ε₂ i j (slSigma L.θ 3 A) := by
  have hstd : (stdTau F n₀).comp (L.ε i) = (L.ε i).comp (slSigma L.θ 2) :=
    MonoidHom.ext fun A => L.stdTau_ε i A
  have hstdj : (stdTau F n₀).comp (L.ε j) = (L.ε j).comp (slSigma L.θ 2) :=
    MonoidHom.ext fun A => L.stdTau_ε j A
  have h : (stdTau F n₀).comp (L.ε₂ i j) = (L.ε₂ i j).comp (slSigma L.θ 3) := by
    apply sl3_hom_ext
    · calc ((stdTau F n₀).comp (L.ε₂ i j)).comp (WeakCT.blk L.Fld 0)
          = (stdTau F n₀).comp ((L.ε₂ i j).comp (WeakCT.blk L.Fld 0)) :=
            MonoidHom.comp_assoc _ _ _
        _ = (stdTau F n₀).comp (L.ε i) := by rw [L.ε₂_left i j hij h3]
        _ = (L.ε i).comp (slSigma L.θ 2) := hstd
        _ = ((L.ε₂ i j).comp (WeakCT.blk L.Fld 0)).comp (slSigma L.θ 2) := by
              rw [L.ε₂_left i j hij h3]
        _ = (L.ε₂ i j).comp ((WeakCT.blk L.Fld 0).comp (slSigma L.θ 2)) :=
              MonoidHom.comp_assoc _ _ _
        _ = (L.ε₂ i j).comp ((slSigma L.θ 3).comp (WeakCT.blk L.Fld 0)) := by
              rw [show (WeakCT.blk L.Fld 0).comp (slSigma L.θ 2) =
                (slSigma L.θ 3).comp (WeakCT.blk L.Fld 0) from
                MonoidHom.ext fun A => (slSigma_blk L.θ 0 A).symm]
        _ = ((L.ε₂ i j).comp (slSigma L.θ 3)).comp (WeakCT.blk L.Fld 0) :=
              (MonoidHom.comp_assoc _ _ _).symm
    · calc ((stdTau F n₀).comp (L.ε₂ i j)).comp (WeakCT.blk L.Fld 1)
          = (stdTau F n₀).comp ((L.ε₂ i j).comp (WeakCT.blk L.Fld 1)) :=
            MonoidHom.comp_assoc _ _ _
        _ = (stdTau F n₀).comp (L.ε j) := by rw [L.ε₂_right i j hij h3]
        _ = (L.ε j).comp (slSigma L.θ 2) := hstdj
        _ = ((L.ε₂ i j).comp (WeakCT.blk L.Fld 1)).comp (slSigma L.θ 2) := by
              rw [L.ε₂_right i j hij h3]
        _ = (L.ε₂ i j).comp ((WeakCT.blk L.Fld 1).comp (slSigma L.θ 2)) :=
              MonoidHom.comp_assoc _ _ _
        _ = (L.ε₂ i j).comp ((slSigma L.θ 3).comp (WeakCT.blk L.Fld 1)) := by
              rw [show (WeakCT.blk L.Fld 1).comp (slSigma L.θ 2) =
                (slSigma L.θ 3).comp (WeakCT.blk L.Fld 1) from
                MonoidHom.ext fun A => (slSigma_blk L.θ 1 A).symm]
        _ = ((L.ε₂ i j).comp (slSigma L.θ 3)).comp (WeakCT.blk L.Fld 1) :=
              (MonoidHom.comp_assoc _ _ _).symm
  exact DFunLike.congr_fun h A

theorem ε₂_mem_stdFix_iff {i j : Fin D.rank} (hij : i < j)
    (h3 : coxeterMatrix D.isFiniteType i j = 3) (A : SL(3, L.Fld)) :
    L.ε₂ i j A ∈ stdFix F n₀ ↔ A ∈ slSU L.θ 3 := by
  rw [mem_stdFix_iff, ← stdTau_apply, L.stdTau_ε₂ hij h3, (L.ε₂_inj i j hij h3).eq_iff,
    mem_slSU_iff]

theorem ε_torusHom_mem (i : Fin D.rank) (a : L.Fldˣ) :
    L.ε i (WeakCT.torusHom L.Fld a) ∈ H i := by
  have h : L.ε i (WeakCT.torusHom L.Fld a) ∈ Set.range fun s => L.ε i (WeakCT.torusHom L.Fld s) :=
    ⟨a, rfl⟩
  rwa [L.diag i] at h

theorem torus_commute (hext : SteinbergExtras D n H) :
    Pairwise fun i j => ∀ x y : L.Fldˣ,
      Commute (((L.ε i).comp (WeakCT.torusHom L.Fld)) x)
        (((L.ε j).comp (WeakCT.torusHom L.Fld)) y) :=
  fun i j _ x y => hext.torus_commute i j _ (L.ε_torusHom_mem i x) _ (L.ε_torusHom_mem j y)

@[expose] noncomputable def torusMap (hext : SteinbergExtras D n H) :
    (Fin D.rank → L.Fldˣ) →* K :=
  MonoidHom.noncommPiCoprod (fun i => (L.ε i).comp (WeakCT.torusHom L.Fld)) (L.torus_commute hext)

theorem torusMap_injective (hext : SteinbergExtras D n H) :
    Function.Injective (L.torusMap hext) := by
  have hrange : ∀ i, ((L.ε i).comp (WeakCT.torusHom L.Fld)).range = H i := by
    intro i
    apply SetLike.coe_injective
    change Set.range (fun s => L.ε i (WeakCT.torusHom L.Fld s)) = (H i : Set K)
    rw [L.diag i]
  refine MonoidHom.injective_noncommPiCoprod_of_iSupIndep
    (fun i => (L.ε i).comp (WeakCT.torusHom L.Fld)) ?_ ?_
  · rw [show (fun i => ((L.ε i).comp (WeakCT.torusHom L.Fld)).range) = H from funext hrange]
    exact hext.torus_iSupIndep
  · exact fun i => (L.ε_inj i).comp (WeakCT.torusHom_injective)

theorem range_torusMap (hext : SteinbergExtras D n H) : (L.torusMap hext).range = ⨆ i, H i := by
  have hrange : ∀ i, ((L.ε i).comp (WeakCT.torusHom L.Fld)).range = H i := by
    intro i
    apply SetLike.coe_injective
    change Set.range (fun s => L.ε i (WeakCT.torusHom L.Fld s)) = (H i : Set K)
    rw [L.diag i]
  change (MonoidHom.noncommPiCoprod (fun i => (L.ε i).comp (WeakCT.torusHom L.Fld))
    (L.torus_commute hext)).range = ⨆ i, H i
  rw [MonoidHom.noncommPiCoprod_range]
  exact iSup_congr hrange

theorem stdTau_torusMap (hext : SteinbergExtras D n H) (a : Fin D.rank → L.Fldˣ) :
    stdTau F n₀ (L.torusMap hext a) =
      L.torusMap hext (fun i => (Units.map L.θ.toMonoidHom (a i))⁻¹) := by
  change stdTau F n₀ (MonoidHom.noncommPiCoprod
      (fun i => (L.ε i).comp (WeakCT.torusHom L.Fld)) (L.torus_commute hext) a) =
    MonoidHom.noncommPiCoprod (fun i => (L.ε i).comp (WeakCT.torusHom L.Fld))
      (L.torus_commute hext) (fun i => (Units.map L.θ.toMonoidHom (a i))⁻¹)
  rw [MonoidHom.noncommPiCoprod_apply, MonoidHom.noncommPiCoprod_apply,
    Finset.map_noncommProd]
  apply Finset.noncommProd_congr rfl
  intro i _
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  rw [L.stdTau_ε, slSigma_torusHom]

end StdLevi

variable {Kf : Type} [Field Kf] [Finite Kf] {f : ℕ} [CharP Kf 2] {Fld : Type} [Field Fld]

private theorem hmbLevi_transpose_map_map {K K' : Type*} [Field K] [Field K']
    {σ : K ≃+* K} (θ : K' →+* K') (κ : K ≃+* K') (hκ : ∀ c, κ (σ c) = θ (κ c))
    {m : ℕ} (A : Matrix (Fin m) (Fin m) K) :
    ((A.map κ).map θ)ᵀ = ((A.map σ)ᵀ).map κ := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  exact (hκ (A j i)).symm

private theorem hmbLevi_map_symm_map_sigma {K K' : Type*} [Field K] [Field K']
    {σ : K ≃+* K} (θ : K' →+* K') (κ : K ≃+* K') (hκ : ∀ c, κ (σ c) = θ (κ c))
    {m : ℕ} (A : Matrix (Fin m) (Fin m) K') :
    (A.map κ.symm).map σ = (A.map θ).map κ.symm := by
  ext i j
  apply κ.injective
  simp only [Matrix.map_apply]
  rw [hκ, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

private theorem hmbLevi_map_symm_map {K K' : Type*} [Field K] [Field K'] (κ : K ≃+* K')
    {m : ℕ} (A : Matrix (Fin m) (Fin m) K') : (A.map κ.symm).map κ = A := by
  ext i j
  simp

theorem range_suToSL (θ : Fld →+* Fld) (κ : Kf ≃+* Fld)
    (hκ : ∀ c, κ (unitaryInvolution Kf 2 f c) = θ (κ c)) (m : ℕ) :
    (suToSL (f := f) κ m).range = slSU θ m := by
  refine le_antisymm ?_ ?_
  · rintro A ⟨B, rfl⟩
    rw [mem_slSU_iff]
    refine inv_eq_of_mul_eq_one_right ?_
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose,
      Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.map_apply_coe, coe_suToSL]
    set Bm : Matrix (Fin m) (Fin m) Kf := ((B : GL (Fin m) Kf) : Matrix (Fin m) (Fin m) Kf)
      with hBm
    have hBm_iso : conjTr (unitaryInvolution Kf 2 f) Bm * Bm = 1 := by
      rw [hBm]; exact B.2.2
    change ((Bm.map κ).map θ)ᵀ * Bm.map κ = 1
    rw [hmbLevi_transpose_map_map θ κ hκ, ← Matrix.map_mul]
    change (conjTr (unitaryInvolution Kf 2 f) Bm * Bm).map κ = 1
    rw [hBm_iso]
    simp
  · intro A hA
    rw [mem_slSU_iff] at hA
    have hMA : ((A : Matrix (Fin m) (Fin m) Fld).map θ)ᵀ *
        (A : Matrix (Fin m) (Fin m) Fld) = 1 := by
      have hAdj : Matrix.adjugate ((A : Matrix (Fin m) (Fin m) Fld).map θ)ᵀ =
          (A : Matrix (Fin m) (Fin m) Fld) := by
        have h := congrArg (fun g : SL(m, Fld) => (g : Matrix (Fin m) (Fin m) Fld)) hA
        simpa only [coe_slSigma] using h
      calc ((A : Matrix (Fin m) (Fin m) Fld).map θ)ᵀ * (A : Matrix (Fin m) (Fin m) Fld)
          = ((A : Matrix (Fin m) (Fin m) Fld).map θ)ᵀ *
              Matrix.adjugate ((A : Matrix (Fin m) (Fin m) Fld).map θ)ᵀ := by rw [hAdj]
        _ = 1 := by
              rw [Matrix.mul_adjugate, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
                ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one, one_smul]
    set Bm : Matrix (Fin m) (Fin m) Kf := (A : Matrix (Fin m) (Fin m) Fld).map κ.symm with hBm
    have hBm_det : Bm.det = 1 := by
      rw [hBm]
      change ((κ.symm : Fld →+* Kf).mapMatrix (A : Matrix (Fin m) (Fin m) Fld)).det = 1
      rw [← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one]
    have hBm_det_ne : Bm.det ≠ 0 := by rw [hBm_det]; exact one_ne_zero
    have hBm_iso : conjTr (unitaryInvolution Kf 2 f) Bm * Bm = 1 := by
      have hmapσ : Bm.map (unitaryInvolution Kf 2 f) =
          ((A : Matrix (Fin m) (Fin m) Fld).map θ).map κ.symm := by
        rw [hBm]
        exact hmbLevi_map_symm_map_sigma θ κ hκ _
      calc conjTr (unitaryInvolution Kf 2 f) Bm * Bm
          = (Bm.map (unitaryInvolution Kf 2 f))ᵀ * Bm := rfl
        _ = ((((A : Matrix (Fin m) (Fin m) Fld).map θ).map κ.symm))ᵀ * Bm := by rw [hmapσ]
        _ = ((((A : Matrix (Fin m) (Fin m) Fld).map θ)ᵀ).map κ.symm) * Bm := by
              rw [← Matrix.transpose_map]
        _ = ((((A : Matrix (Fin m) (Fin m) Fld).map θ)ᵀ).map κ.symm) *
              ((A : Matrix (Fin m) (Fin m) Fld).map κ.symm) := by rw [hBm]
        _ = ((((A : Matrix (Fin m) (Fin m) Fld).map θ)ᵀ) *
              (A : Matrix (Fin m) (Fin m) Fld)).map κ.symm := by
              rw [Matrix.map_mul]
        _ = (1 : Matrix (Fin m) (Fin m) Kf) := by rw [hMA]; simp
    refine MonoidHom.mem_range.mpr ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Bm hBm_det_ne,
      ?_⟩, ?_⟩
    · rw [mem_SUid]
      exact ⟨by rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hBm_det],
        by rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hBm_iso]⟩
    · apply Subtype.ext
      rw [coe_suToSL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hBm]
      exact hmbLevi_map_symm_map κ _

theorem suToSL_injective (κ : Kf ≃+* Fld) (m : ℕ) : Function.Injective (suToSL (f := f) κ m) := by
  intro A B h
  have h1 : (((A : GL (Fin m) Kf) : Matrix (Fin m) (Fin m) Kf).map κ) =
      (((B : GL (Fin m) Kf) : Matrix (Fin m) (Fin m) Kf).map κ) := by
    have h2 := congrArg (fun x : SL(m, Fld) => (x : Matrix (Fin m) (Fin m) Fld)) h
    simpa only [coe_suToSL] using h2
  exact Subtype.ext (Units.ext (Matrix.map_injective κ.injective h1))

end CFSG.ClassicalInvolution.Phan.PhanE
