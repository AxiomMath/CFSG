module

public import CFSG.RankThree.PartOne.KF.R8LeviA

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ Matrix

@[expose] def fidx : (Σ _ : Fin 2, Fin 2) ≃ Fin 4 :=
  (Equiv.sigmaEquivProd (Fin 2) (Fin 2)).trans finProdFinEquiv

@[expose] noncomputable def fvec (K : Type) [Field K] [Finite K] [CharP K 2] (i : Fin 4) :
    QV K (Fin 2) :=
  Pi.single (fidx.symm i).1 (qBasis K (fidx.symm i).2)

@[expose] noncomputable def fbasis (K : Type) [Field K] [Finite K] [CharP K 2] :
    Module.Basis (Fin 4) K (QV K (Fin 2)) :=
  (Pi.basis fun _ : Fin 2 => qBasis K).reindex fidx

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem fbasis_apply (i : Fin 4) : fbasis K i = fvec K i := by
  simp [fbasis, fvec]

theorem fbasis_repr (v : QV K (Fin 2)) (k : Fin 4) :
    (fbasis K).repr v k = (qBasis K).repr (v (fidx.symm k).1) (fidx.symm k).2 := by
  simp [fbasis]

@[expose] noncomputable def adGL :
    (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) ≃* GL (Fin 4) K :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (QV K (Fin 2))).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (fbasis K)).toMulEquiv)

theorem det_adGL (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) :
    ((adGL g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = (LinearEquiv.det g : K) := by
  rw [LinearEquiv.coe_det]
  exact LinearMap.det_toMatrix (fbasis K) (g : QV K (Fin 2) →ₗ[K] QV K (Fin 2))

theorem adGL_apply (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (k l : Fin 4) :
    ((adGL g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) k l =
      (fbasis K).repr (g (fbasis K l)) k := by
  show LinearMap.toMatrix (fbasis K) (fbasis K) (g : QV K (Fin 2) →ₗ[K] QV K (Fin 2)) k l = _
  rw [LinearMap.toMatrix_apply]
  rfl

@[expose] noncomputable def adHom : ↥(M8 K) →* Matrix.SpecialLinearGroup (Fin 4) K where
  toFun g := ⟨((adGL (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K), by
    rw [det_adGL, (mem_M8_iff _).1 g.2]
    simp⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Subtype.ext
    show ((adGL ((g * h : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = _
    rw [Subgroup.coe_mul, map_mul, Units.val_mul]
    rfl

theorem adHom_bijective : Function.Bijective (adHom (K := K)) := by
  refine ⟨fun g h hgh => ?_, fun X => ?_⟩
  · apply Subtype.ext
    apply adGL.injective
    apply Units.ext
    exact congrArg Subtype.val hgh
  · refine ⟨⟨adGL.symm (Matrix.SpecialLinearGroup.toGL X), (mem_M8_iff _).2 ?_⟩, ?_⟩
    · apply Units.ext
      have h1 := det_adGL (adGL.symm (Matrix.SpecialLinearGroup.toGL X))
      rw [MulEquiv.apply_symm_apply] at h1
      rw [← h1]
      simp
    · apply Subtype.ext
      show ((adGL (adGL.symm (Matrix.SpecialLinearGroup.toGL X)) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = _
      rw [MulEquiv.apply_symm_apply]
      rfl

@[expose] noncomputable def adSL : ↥(M8 K) ≃* Matrix.SpecialLinearGroup (Fin 4) K :=
  MulEquiv.ofBijective adHom adHom_bijective

theorem adSL_coe (g : ↥(M8 K)) :
    ((adSL g : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((adGL (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) := rfl

theorem adSL_apply (g : ↥(M8 K)) (k l : Fin 4) :
    (adSL g : Matrix (Fin 4) (Fin 4) K) k l =
      (fbasis K).repr ((g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (fvec K l)) k := by
  rw [adSL_coe, adGL_apply, fbasis_apply]

theorem apply_fvec (g : ↥(M8 K)) (l : Fin 4) :
    (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (fvec K l) =
      ∑ k, (adSL g : Matrix (Fin 4) (Fin 4) K) k l • fvec K k := by
  conv_lhs => rw [← (fbasis K).sum_repr ((g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (fvec K l))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [adSL_apply, fbasis_apply]

theorem adSL_eq_of_apply {g : ↥(M8 K)} {X : Matrix (Fin 4) (Fin 4) K}
    (h : ∀ l, (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (fvec K l) = ∑ k, X k l • fvec K k) :
    (adSL g : Matrix (Fin 4) (Fin 4) K) = X := by
  ext k l
  rw [adSL_apply, h l, map_sum]
  simp only [map_smul, ← fbasis_apply, Module.Basis.repr_self, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply, smul_eq_mul]
  simp

theorem eq_of_apply_fvec {g h : ↥(M8 K)}
    (hgh : ∀ l, (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (fvec K l) =
      (h : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (fvec K l)) : g = h := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (fbasis K).ext
  intro l
  rw [fbasis_apply]
  exact hgh l

@[expose] noncomputable def eM {i j : Fin 4} (h : i ≠ j) (c : K) : ↥(M8 K) :=
  adSL.symm (Matrix.SpecialLinearGroup.transvection h c)

theorem adSL_eM {i j : Fin 4} (h : i ≠ j) (c : K) :
    adSL (eM h c) = Matrix.SpecialLinearGroup.transvection h c := by
  simp [eM]

@[expose] noncomputable def psl :
    Equiv.Perm (Fin 4) →* Matrix.SpecialLinearGroup (Fin 4) K where
  toFun σ := ⟨((permGL σ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K), det_permGL σ⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' σ τ := by
    apply Subtype.ext
    show ((permGL (σ * τ) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((permGL σ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((permGL τ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    rw [map_mul, Units.val_mul]

omit [Finite K] in
theorem coe_psl (σ : Equiv.Perm (Fin 4)) :
    ((psl σ : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      σ⁻¹.permMatrix K := rfl

omit [Finite K] in
theorem psl_conj_apply (σ : Equiv.Perm (Fin 4)) (M : Matrix (Fin 4) (Fin 4) K) (a b : Fin 4) :
    (((psl σ : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * M *
      (((psl σ)⁻¹ : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) a b =
      M (σ.symm a) (σ.symm b) := by
  have hinv : (((psl σ)⁻¹ : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      σ.permMatrix K := by
    rw [← map_inv]
    show ((σ⁻¹)⁻¹).permMatrix K = _
    rw [inv_inv]
  rw [hinv, coe_psl]
  have h1 : (σ⁻¹.permMatrix K) * M = M.submatrix (σ⁻¹ : Equiv.Perm (Fin 4)) id :=
    PEquiv.toMatrix_toPEquiv_mul _ _
  have h2 : (M.submatrix (σ⁻¹ : Equiv.Perm (Fin 4)) id) * σ.permMatrix K =
      (M.submatrix (σ⁻¹ : Equiv.Perm (Fin 4)) id).submatrix id σ.symm :=
    PEquiv.mul_toMatrix_toPEquiv _ _
  rw [h1, h2]
  rfl

@[expose] noncomputable def pM : Equiv.Perm (Fin 4) →* ↥(M8 K) :=
  (adSL (K := K)).symm.toMonoidHom.comp psl

theorem adSL_pM (σ : Equiv.Perm (Fin 4)) : adSL (pM σ : ↥(M8 K)) = psl σ := by
  simp [pM]

end CFSG.RankThree.PartOne.K1320
