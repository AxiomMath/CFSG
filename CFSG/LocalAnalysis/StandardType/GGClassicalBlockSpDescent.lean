module

public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp
public import CFSG.HardMathSupport.Foote.ModuleExclusions.Hilbert90
public import CFSG.Open.StatedAPI
public import CFSG.ClassicalGroups.Unitary.Form
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoFixedField
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoGeneralLinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition Matrix
open CFSG.ComponentClassification.CatalogueBLinearTwoFixed
open CFSG.Open.StatedAPI

private lemma ggJSt3_sigma_sq_one {K : Type} [Field K] (σ : K ≃+* K)
    (hσ2 : ∀ x, σ (σ x) = x) : σ ^ 2 = 1 := by
  ext x
  rw [pow_two]
  exact hσ2 x

private lemma ggJSt3_orderOf_sigma {K : Type} [Field K] (σ : K ≃+* K)
    (hσ : σ ≠ RingEquiv.refl K) (hσ2 : ∀ x, σ (σ x) = x) : orderOf σ = 2 :=
  orderOf_eq_prime (ggJSt3_sigma_sq_one σ hσ2) hσ

private lemma ggJSt3_coe_map {K : Type} [Field K] {N : ℕ} (σ : K ≃+* K) (a : GL (Fin N) K) :
    ((a.map σ.toRingHom : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
      = (a : Matrix (Fin N) (Fin N) K).map σ := rfl

theorem exists_matrix_hilbert90 {K : Type} [Field K] [Finite K] {N : ℕ} (σ : K ≃+* K)
    (hσ : σ ≠ RingEquiv.refl K) (hσ2 : ∀ x, σ (σ x) = x) (A : GL (Fin N) K)
    (hA : A * A.map σ.toRingHom = 1) :
    ∃ P : GL (Fin N) K, A = P⁻¹ * P.map σ.toRingHom := by
  have hord : orderOf σ = 2 := ggJSt3_orderOf_sigma σ hσ hσ2
  have hAmat : (A : Matrix (Fin N) (Fin N) K) * ((A : Matrix (Fin N) (Fin N) K).map σ) = 1 := by
    have h := congrArg (fun x : GL (Fin N) K => (x : Matrix (Fin N) (Fin N) K)) hA
    simpa [ggJSt3_coe_map] using h
  have hAi : CFSG.HardMathSupport.Foote.ModuleExclusions.Ai σ
      (A : Matrix (Fin N) (Fin N) K) 2 = 1 := by
    simpa [CFSG.HardMathSupport.Foote.ModuleExclusions.Ai] using hAmat
  obtain ⟨B, hBdet, hAB⟩ :=
    CFSG.HardMathSupport.Foote.ModuleExclusions.speiser σ (A : Matrix (Fin N) (Fin N) K) 2
      hord (by norm_num) hAi
  let Bgl : GL (Fin N) K := Matrix.GeneralLinearGroup.mkOfDetNeZero B hBdet
  have hBgl : (Bgl : Matrix (Fin N) (Fin N) K) = B :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero B hBdet
  have hABgl : A * Bgl.map σ.toRingHom = Bgl := by
    apply Units.ext
    simpa [ggJSt3_coe_map, hBgl] using hAB
  have hmap : Bgl.map σ.toRingHom = A⁻¹ * Bgl := by
    calc Bgl.map σ.toRingHom = A⁻¹ * (A * Bgl.map σ.toRingHom) := by rw [inv_mul_cancel_left]
      _ = A⁻¹ * Bgl := by rw [hABgl]
  refine ⟨Bgl⁻¹, ?_⟩
  rw [map_inv, hmap, _root_.mul_inv_rev, inv_inv]
  group

private lemma ggJSt3_hilbert90 {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    (σ : K ≃+* K) (hσ : σ ≠ RingEquiv.refl K) (hσ2 : ∀ x, σ (σ x) = x) (A : GL ι K)
    (hA : A * A.map σ.toRingHom = 1) :
    ∃ P : GL ι K, A = P⁻¹ * P.map σ.toRingHom := by
  have hord : orderOf σ = 2 := ggJSt3_orderOf_sigma σ hσ hσ2
  have hAmat : (A : Matrix ι ι K) * ((A : Matrix ι ι K).map σ) = 1 := by
    have h := congrArg (fun x : GL ι K => (x : Matrix ι ι K)) hA
    simpa [ggJSt3_coe_map] using h
  have hAi : CFSG.HardMathSupport.Foote.ModuleExclusions.Ai σ (A : Matrix ι ι K) 2 = 1 := by
    simpa [CFSG.HardMathSupport.Foote.ModuleExclusions.Ai] using hAmat
  obtain ⟨B, hBdet, hAB⟩ :=
    CFSG.HardMathSupport.Foote.ModuleExclusions.speiser σ (A : Matrix ι ι K) 2
      hord (by norm_num) hAi
  let Bgl : GL ι K := Matrix.GeneralLinearGroup.mkOfDetNeZero B hBdet
  have hBgl : (Bgl : Matrix ι ι K) = B :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero B hBdet
  have hABgl : A * Bgl.map σ.toRingHom = Bgl := by
    apply Units.ext
    simpa [ggJSt3_coe_map, hBgl] using hAB
  have hmap : Bgl.map σ.toRingHom = A⁻¹ * Bgl := by
    calc Bgl.map σ.toRingHom = A⁻¹ * (A * Bgl.map σ.toRingHom) := by rw [inv_mul_cancel_left]
      _ = A⁻¹ * Bgl := by rw [hABgl]
  refine ⟨Bgl⁻¹, ?_⟩
  rw [map_inv, hmap, _root_.mul_inv_rev, inv_inv]
  group

private lemma ggJSt3_map_pow {ι K L : Type} [Fintype ι] [DecidableEq ι] [Semiring K]
    [Semiring L] (φ : K →+* L) (M : Matrix ι ι K) (n : ℕ) :
    (M ^ n).map φ = (M.map φ) ^ n := by
  have h := map_pow (RingHom.mapMatrix φ) M n
  simpa only [RingHom.mapMatrix_apply] using h

private lemma ggJSt3_isSemisimple {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (M : Matrix ι ι K) (n : ℕ) (hn : (n : AlgebraicClosure K) ≠ 0) (hM : M ^ n = 1) :
    Module.End.IsSemisimple (Matrix.toLin' (M.map (algebraMap K (AlgebraicClosure K)))) := by
  have hfpow : (Matrix.toLin' (M.map (algebraMap K (AlgebraicClosure K)))) ^ n = 1 := by
    have h1 : (M ^ n).map (algebraMap K (AlgebraicClosure K)) = 1 := by
      rw [hM]
      exact map_one (RingHom.mapMatrix (algebraMap K (AlgebraicClosure K)))
    rw [← Matrix.toLin'_pow, ← ggJSt3_map_pow, h1]
    exact map_one (Matrix.toLinAlgEquiv' (R := AlgebraicClosure K) (n := ι))
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (Polynomial.X : Polynomial (AlgebraicClosure K)) ^ n - 1) ?_ ?_
  · exact (Polynomial.X_pow_sub_one_separable_iff.mpr hn).squarefree
  · simpa [Polynomial.aeval_X, hfpow]

private lemma ggJSt3_eigDim_eq_rootMultiplicity {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (M : Matrix ι ι K) (n : ℕ) (hn : (n : AlgebraicClosure K) ≠ 0)
    (hM : M ^ n = 1) (l : AlgebraicClosure K) :
    eigDim M l = ((M.charpoly).map (algebraMap K (AlgebraicClosure K))).rootMultiplicity l := by
  have hf : Module.End.IsSemisimple
      (Matrix.toLin' (M.map (algebraMap K (AlgebraicClosure K)))) :=
    ggJSt3_isSemisimple M n hn hM
  have hchar : (Matrix.toLin' (M.map (algebraMap K (AlgebraicClosure K)))).charpoly =
      (M.charpoly).map (algebraMap K (AlgebraicClosure K)) := by
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map]
  unfold eigDim
  rw [← hchar, ← LinearMap.finrank_maxGenEigenspace_eq,
    Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
      (Module.End.IsSemisimple.isFinitelySemisimple hf) l]

private noncomputable def ggJSt3_polyExp {k : Type} [Field k] (inst : DecidableEq k) 
    (p : Polynomial k) : ℕ :=
  letI := inst
  (Polynomial.rootMultiplicity 1 p / 2) ^ 2 +
    (∑ l ∈ p.roots.toFinset.erase 1,
      Polynomial.rootMultiplicity l p * (Polynomial.rootMultiplicity l p - 1) / 2) / 2

private lemma ggJSt3_blockExp_eq_polyExp {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (M : Matrix ι ι K) (n : ℕ) (hn : (n : AlgebraicClosure K) ≠ 0) (hM : M ^ n = 1) :
    blockExp false M = ggJSt3_polyExp (Classical.decEq (AlgebraicClosure K))
      ((M.charpoly).map (algebraMap K (AlgebraicClosure K))) := by
  classical
  rw [blockExp, ggJSt3_polyExp]
  simp only [Bool.false_eq_true, if_false]
  congr 1
  · rw [ggJSt3_eigDim_eq_rootMultiplicity M n hn hM 1]
  · congr 1
    exact Finset.sum_congr rfl fun l _ => by
      rw [ggJSt3_eigDim_eq_rootMultiplicity M n hn hM l]

private lemma ggJSt3_polyExp_map {F K : Type} [Field F] [Field K] [Algebra F K]
    (p : Polynomial F) :
    ggJSt3_polyExp (Classical.decEq (AlgebraicClosure K))
        (p.map (algebraMap F (AlgebraicClosure K))) =
      ggJSt3_polyExp (Classical.decEq (AlgebraicClosure F))
        (p.map (algebraMap F (AlgebraicClosure F))) := by
  classical
  let eeA : AlgebraicClosure F →ₐ[F] AlgebraicClosure K := IsAlgClosed.lift
  let ee : AlgebraicClosure F →+* AlgebraicClosure K := eeA
  have hcomp : ee.comp (algebraMap F (AlgebraicClosure F)) =
      algebraMap F (AlgebraicClosure K) := by
    ext x
    exact eeA.commutes x
  set pF : Polynomial (AlgebraicClosure F) := p.map (algebraMap F (AlgebraicClosure F)) with hpF
  have hp : p.map (algebraMap F (AlgebraicClosure K)) = pF.map ee := by
    rw [hpF, Polynomial.map_map, hcomp]
  have hsplit : (pF.map ee).roots = pF.roots.map ee :=
    Polynomial.Splits.roots_map (IsAlgClosed.splits pF) ee
  have hs : (pF.map ee).roots.toFinset.erase 1 = (pF.roots.toFinset.erase 1).image ee := by
    rw [hsplit, Multiset.toFinset_map, ← map_one ee,
      ← Finset.image_erase (f := ee) ee.injective pF.roots.toFinset 1]
  simp only [ggJSt3_polyExp]
  rw [hp]
  congr 1
  · conv_lhs => rw [← map_one ee]
    rw [← Polynomial.eq_rootMultiplicity_map (p := pF) (f := ee) ee.injective 1]
  · congr 1
    rw [hs, Finset.sum_image]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [Polynomial.eq_rootMultiplicity_map (p := pF) (f := ee) ee.injective l]
    · intro x _ y _ hxy
      exact ee.injective hxy

private lemma ggJSt3_blockExp_map {ι F K : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Field K] [Algebra F K] (M : Matrix ι ι F) (n : ℕ) (hn : (n : AlgebraicClosure F) ≠ 0)
    (hM : M ^ n = 1) :
    blockExp false (M.map (algebraMap F K)) = blockExp false M := by
  classical
  have hnF : (n : F) ≠ 0 := by
    intro h
    exact hn (by rw [← map_natCast (algebraMap F (AlgebraicClosure F)) n, h, map_zero])
  have hnK : (n : K) ≠ 0 := by
    intro h
    exact hnF ((algebraMap F K).injective (by rw [map_natCast, h, map_zero]))
  have hnAC : (n : AlgebraicClosure K) ≠ 0 := by
    intro h
    exact hnK ((algebraMap K (AlgebraicClosure K)).injective
      (by rw [map_natCast, h, map_zero]))
  have hMK : (M.map (algebraMap F K)) ^ n = 1 := by
    rw [← ggJSt3_map_pow, hM]
    exact map_one (RingHom.mapMatrix (algebraMap F K))
  have hpoly : ((M.map (algebraMap F K)).charpoly).map (algebraMap K (AlgebraicClosure K)) =
      (M.charpoly).map (algebraMap F (AlgebraicClosure K)) := by
    have hcomp2 : (algebraMap K (AlgebraicClosure K)).comp (algebraMap F K) =
        algebraMap F (AlgebraicClosure K) :=
      (IsScalarTower.algebraMap_eq F K (AlgebraicClosure K)).symm
    rw [Matrix.charpoly_map, Polynomial.map_map, hcomp2]
  rw [ggJSt3_blockExp_eq_polyExp (M.map (algebraMap F K)) n hnAC hMK,
    ggJSt3_blockExp_eq_polyExp M n hn hM, hpoly]
  exact ggJSt3_polyExp_map (p := M.charpoly)

private lemma ggJSt3_blockExp_conj {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (X M : GL ι K) (n : ℕ) (hn : (n : AlgebraicClosure K) ≠ 0) (hM : M ^ n = 1) :
    blockExp false ((X * M * X⁻¹ : GL ι K) : Matrix ι ι K) =
      blockExp false (M : Matrix ι ι K) := by
  classical
  have hconj : (X * M * X⁻¹ : GL ι K) ^ n = 1 := by
    have h := map_pow (MulAut.conj X) M n
    rw [hM, map_one, MulAut.conj_apply] at h
    exact h.symm
  have hMK : ((X * M * X⁻¹ : GL ι K) : Matrix ι ι K) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, hconj, Units.val_one]
  have hMmat : (M : Matrix ι ι K) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, hM, Units.val_one]
  have hchar : ((X * M * X⁻¹ : GL ι K) : Matrix ι ι K).charpoly =
      (M : Matrix ι ι K).charpoly := by
    have hcoe : ((X * M * X⁻¹ : GL ι K) : Matrix ι ι K) =
        (X : Matrix ι ι K) * (M : Matrix ι ι K) * ((X⁻¹ : GL ι K) : Matrix ι ι K) := by
      simp only [Units.val_mul]
    rw [hcoe]
    calc ((X : Matrix ι ι K) * (M : Matrix ι ι K) * ((X⁻¹ : GL ι K) : Matrix ι ι K)).charpoly
        = (((X⁻¹ : GL ι K) : Matrix ι ι K) *
            ((X : Matrix ι ι K) * (M : Matrix ι ι K))).charpoly :=
          Matrix.charpoly_mul_comm _ _
      _ = (M : Matrix ι ι K).charpoly := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [ggJSt3_blockExp_eq_polyExp ((X * M * X⁻¹ : GL ι K) : Matrix ι ι K) n hn hMK,
    ggJSt3_blockExp_eq_polyExp (M : Matrix ι ι K) n hn hMmat, hchar]

private def ggJSt3_fixedSubgroup {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (σ : K ≃+* K) : Subgroup (GL ι K) where
  carrier := {X | X.map σ.toRingHom = X}
  one_mem' := map_one _
  mul_mem' {a b} ha hb := by
    change (a * b).map σ.toRingHom = a * b
    rw [map_mul, ha, hb]
  inv_mem' {a} ha := by
    change (a⁻¹).map σ.toRingHom = a⁻¹
    rw [map_inv, ha]

private noncomputable def ggJSt3_descendMatrix {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (σ : K ≃+* K) (M : Matrix ι ι K) (hM : ∀ i j, σ (M i j) = M i j) :
    Matrix ι ι ↥(fixedField K σ) :=
  fun i j => ⟨M i j, (mem_fixedField_iff K σ (M i j)).mpr (hM i j)⟩

private lemma ggJSt3_descendMatrix_map {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (σ : K ≃+* K) (M : Matrix ι ι K) (hM : ∀ i j, σ (M i j) = M i j) :
    (ggJSt3_descendMatrix σ M hM).map (algebraMap ↥(fixedField K σ) K) = M := by
  ext i j
  rfl

private noncomputable def ggJSt3_descendGL {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (σ : K ≃+* K) (X : GL ι K) (hX : X.map σ.toRingHom = X) :
    GL ι ↥(fixedField K σ) := by
  have hentry : ∀ i j, σ ((X : Matrix ι ι K) i j) = (X : Matrix ι ι K) i j := by
    intro i j
    have h := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K) i j) hX
    simpa [Matrix.GeneralLinearGroup.val_map_apply, Matrix.map_apply] using h
  refine Matrix.GeneralLinearGroup.mkOfDetNeZero
    (ggJSt3_descendMatrix σ (X : Matrix ι ι K) hentry) ?_
  intro hdet
  have hdetmap : algebraMap ↥(fixedField K σ) K
      ((ggJSt3_descendMatrix σ (X : Matrix ι ι K) hentry).det) = (X : Matrix ι ι K).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ggJSt3_descendMatrix_map]
  rw [hdet, map_zero] at hdetmap
  exact X.det_ne_zero hdetmap.symm

private lemma ggJSt3_descendGL_map {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (σ : K ≃+* K) (X : GL ι K) (hX : X.map σ.toRingHom = X) :
    (ggJSt3_descendGL σ X hX).map (algebraMap ↥(fixedField K σ) K) = X := by
  apply Units.ext
  unfold ggJSt3_descendGL
  rw [Matrix.GeneralLinearGroup.val_map_apply,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, ggJSt3_descendMatrix_map]

private lemma ggJSt3_map_subtype_fixed {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (σ : K ≃+* K) (Y : GL ι ↥(fixedField K σ)) :
    (Y.map (algebraMap ↥(fixedField K σ) K)).map σ.toRingHom =
      Y.map (algebraMap ↥(fixedField K σ) K) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_map_apply, Matrix.GeneralLinearGroup.val_map_apply]
  ext i j
  simp only [Matrix.map_apply]
  exact fixedField_coe K σ (Y i j)

private lemma ggJSt3_descendMatrix_mul {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (σ : K ≃+* K) (M N : Matrix ι ι K)
    (hM : ∀ i j, σ (M i j) = M i j) (hN : ∀ i j, σ (N i j) = N i j) :
    ggJSt3_descendMatrix σ (M * N)
        (fun i j => by
          rw [Matrix.mul_apply, map_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [map_mul, hM i k, hN k j])
      = ggJSt3_descendMatrix σ M hM * ggJSt3_descendMatrix σ N hN := by
  ext i j
  simp [ggJSt3_descendMatrix, Matrix.mul_apply]

private noncomputable def ggJSt3_fixedGL_equiv {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (σ : K ≃+* K) : ↥(ggJSt3_fixedSubgroup (ι := ι) σ) ≃* GL ι ↥(fixedField K σ) where
  toFun X := ggJSt3_descendGL σ X.val X.property
  invFun Y := ⟨Y.map (algebraMap ↥(fixedField K σ) K), ggJSt3_map_subtype_fixed σ Y⟩
  left_inv X := by
    apply Subtype.ext
    exact ggJSt3_descendGL_map σ X.val X.property
  right_inv Y := by
    apply Units.ext
    show (ggJSt3_descendGL σ (Y.map (algebraMap ↥(fixedField K σ) K))
      (ggJSt3_map_subtype_fixed σ Y) : Matrix ι ι ↥(fixedField K σ)) =
        (Y : Matrix ι ι ↥(fixedField K σ))
    unfold ggJSt3_descendGL
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    ext i j
    simp only [ggJSt3_descendMatrix, Matrix.GeneralLinearGroup.val_map_apply, Matrix.map_apply]
    rfl
  map_mul' X Y := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    simp only [ggJSt3_descendGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Subgroup.coe_mul, Units.val_mul, ggJSt3_descendMatrix, Matrix.mul_apply,
      map_sum, map_mul, Subtype.coe_mk]
    push_cast
    rfl

private lemma ggJSt3_cancel_conj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (U X Y : Matrix ι ι K) (hU : IsUnit U.det) (h : Uᵀ * X * U = Uᵀ * Y * U) : X = Y := by
  haveI := Matrix.invertibleOfIsUnitDet U hU
  have h1 : Uᵀ * X = Uᵀ * Y := (Matrix.mul_left_inj_of_invertible (A := U)).mp h
  exact (Matrix.mul_right_inj_of_invertible (A := Uᵀ)).mp h1

private lemma ggJSt3_form_fixed {n : ℕ} {K : Type} [Field K] (σ : K ≃+* K)
    (P A : GL (Fin n ⊕ Fin n) K)
    (hAJ : (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
        (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
        (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))
    (hPA : A = P⁻¹ * P.map σ.toRingHom) :
    ((((P⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
      ((P⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)).map σ) =
      ((P⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
        (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
        ((P⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
  set J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := fromBlocks 0 1 (-1) 0 with hJ
  set Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    ((P⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) with hQ
  set Pm : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    (P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map σ.toRingHom with hPm
  have hσJ : J.map σ.toRingHom = J := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [hJ, Matrix.fromBlocks, Matrix.one_apply, apply_ite ⇑σ.toRingHom, map_one, map_zero]
  have hQσmul : Q.map σ.toRingHom * Pm = 1 := by
    have h : (P⁻¹ : GL (Fin n ⊕ Fin n) K).map σ.toRingHom * P.map σ.toRingHom = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    have h'' := congrArg (fun X : GL (Fin n ⊕ Fin n) K =>
      (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) h
    rw [Units.val_mul, Matrix.GeneralLinearGroup.val_map_apply,
      Matrix.GeneralLinearGroup.val_map_apply] at h''
    rw [← hQ, ← hPm] at h''
    exact h''
  have hPmQσ : Pm * Q.map σ.toRingHom = 1 := by
    have h : P.map σ.toRingHom * (P⁻¹ : GL (Fin n ⊕ Fin n) K).map σ.toRingHom = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have h'' := congrArg (fun X : GL (Fin n ⊕ Fin n) K =>
      (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) h
    rw [Units.val_mul, Matrix.GeneralLinearGroup.val_map_apply,
      Matrix.GeneralLinearGroup.val_map_apply] at h''
    rw [← hQ, ← hPm] at h''
    exact h''
  have hAmat : (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Q * Pm := by
    have h := congrArg (fun X : GL (Fin n ⊕ Fin n) K =>
      (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hPA
    rw [Units.val_mul, Matrix.GeneralLinearGroup.val_map_apply] at h
    rw [← hQ, ← hPm] at h
    exact h
  have hdetPm : IsUnit Pm.det := by
    rw [hPm]
    have h1 : IsUnit (σ.toRingHom ((P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).det)) :=
      RingHom.isUnit_map σ.toRingHom
        (isUnit_iff_ne_zero.mpr (Matrix.GeneralLinearGroup.det_ne_zero P))
    rw [RingHom.map_det, RingHom.mapMatrix_apply] at h1
    exact h1
  have hJ'map : ((Qᵀ * J * Q).map σ.toRingHom) =
      (Q.map σ.toRingHom)ᵀ * J * (Q.map σ.toRingHom) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hσJ]
  have heq1 : Pmᵀ * (Qᵀ * J * Q) * Pm = J := by
    rw [hAmat] at hAJ
    rw [Matrix.transpose_mul] at hAJ
    simpa only [Matrix.mul_assoc] using hAJ
  have heq2 : Pmᵀ * ((Qᵀ * J * Q).map σ.toRingHom) * Pm = J := by
    rw [hJ'map]
    have hassoc : Pmᵀ * ((Q.map σ.toRingHom)ᵀ * J * (Q.map σ.toRingHom)) * Pm =
        (Q.map σ.toRingHom * Pm)ᵀ * J * (Q.map σ.toRingHom * Pm) := by
      rw [Matrix.transpose_mul]
      noncomm_ring
    rw [hassoc, hQσmul, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hgoal : (Qᵀ * J * Q).map σ = Qᵀ * J * Q := by
    simpa only [RingEquiv.coe_toRingHom, RingEquiv.toRingHom_eq_coe] using
      ggJSt3_cancel_conj Pm ((Qᵀ * J * Q).map σ.toRingHom) (Qᵀ * J * Q) hdetPm
        (heq2.trans heq1.symm)
  simpa [hQ, hJ] using hgoal

private lemma ggJSt3_J_eq_fromBlocks {n : ℕ} {F : Type} [Field F] [CharP F 2] :
    Matrix.J (Fin n) F = (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.J, Matrix.fromBlocks, CharTwo.neg_eq]

private lemma ggJSt3_matrix_of_basis {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (J₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (β : Module.Basis (Fin n ⊕ Fin n) F (Fin n ⊕ Fin n → F))
    (hb : ∀ x y, (Matrix.toBilin' J₀) (β x) (β y) =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x y) :
    (Matrix.of fun r c => β c r)ᵀ * J₀ * (Matrix.of fun r c => β c r) =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
  set P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := Matrix.of fun r c => β c r with hP
  have hcol : ∀ c, P *ᵥ Pi.single c 1 = β c := fun c => by
    ext r
    simp [hP, Matrix.mulVec_single_one]
  ext x y
  have h1 := hb x y
  rw [← hcol x, ← hcol y] at h1
  have h2 := congrArg (fun B => B (Pi.single x 1) (Pi.single y 1))
    (Matrix.toBilin'_comp J₀ P P)
  simp only [LinearMap.BilinForm.comp_apply, Matrix.toBilin'_single, Matrix.toLin'_apply] at h2
  rw [← h2]
  exact h1

private lemma ggJSt3_exists_symplectic {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (J₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (hAlt : (Matrix.toBilin' J₀).IsAlt) (hNon : (Matrix.toBilin' J₀).Nondegenerate) :
    ∃ C : GL (Fin n ⊕ Fin n) F,
      (C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ * J₀ *
        (C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
  obtain ⟨m, β, hβ⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J hAlt hNon
  have hm : m = n := by
    have h1 := Module.finrank_eq_card_basis β
    have h2 : Module.finrank F (Fin n ⊕ Fin n → F) = Fintype.card (Fin n ⊕ Fin n) :=
      Module.finrank_eq_card_basis (Pi.basisFun F (Fin n ⊕ Fin n))
    rw [h2, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h1
    omega
  obtain rfl : n = m := hm.symm
  have hb : ∀ x y, (Matrix.toBilin' J₀) (β x) (β y) =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x y := by
    intro x y
    rw [← LinearMap.BilinForm.toMatrix_apply β (Matrix.toBilin' J₀) x y, hβ,
      ggJSt3_J_eq_fromBlocks]
  have hPJ := ggJSt3_matrix_of_basis J₀ β hb
  set P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := Matrix.of fun r c => β c r with hPP
  have hdet : IsUnit P.det := by
    have hPe : P = (Pi.basisFun F (Fin n ⊕ Fin n)).toMatrix β := by
      ext r c
      simp [hPP, Module.Basis.toMatrix_apply]
    rw [hPe, ← Matrix.isUnit_iff_isUnit_det]
    exact @isUnit_of_invertible _ _ _ ((Pi.basisFun F (Fin n ⊕ Fin n)).invertibleToMatrix β)
  refine ⟨Matrix.GeneralLinearGroup.mk'' P hdet, ?_⟩
  rw [Matrix.GeneralLinearGroup.val_mk'']
  simpa [hPP] using hPJ

private lemma ggJSt3_conj_fixed_of_hfix {n : ℕ} {K : Type} [Field K] (σ : K ≃+* K)
    (A P g : GL (Fin n ⊕ Fin n) K) (hPA : A = P⁻¹ * P.map σ.toRingHom)
    (hg : A * g.map σ.toRingHom * A⁻¹ = g) :
    (P * g * P⁻¹).map σ.toRingHom = P * g * P⁻¹ := by
  have hg' : g.map σ.toRingHom = A⁻¹ * g * A := by
    calc g.map σ.toRingHom = A⁻¹ * (A * g.map σ.toRingHom * A⁻¹) * A := by group
      _ = A⁻¹ * g * A := by rw [hg]
  calc (P * g * P⁻¹).map σ.toRingHom
      = P.map σ.toRingHom * g.map σ.toRingHom * (P⁻¹).map σ.toRingHom := by
        rw [map_mul, map_mul, map_inv]
    _ = P.map σ.toRingHom * (A⁻¹ * g * A) * (P⁻¹).map σ.toRingHom := by rw [hg']
    _ = P * g * P⁻¹ := by
        rw [hPA, _root_.mul_inv_rev, inv_inv, map_inv]
        group

private lemma ggJSt3_descend_gram {n : ℕ} {F K : Type} [Field F] [Field K] [Algebra F K]
    (hφ : Function.Injective (algebraMap F K))
    (J₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (J' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (hJ : J₀.map (algebraMap F K) = J')
    (X₀ : GL (Fin n ⊕ Fin n) F) (X : GL (Fin n ⊕ Fin n) K)
    (hX : (X₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map (algebraMap F K) =
      (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))
    (h : (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * J' *
      (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = J') :
    (X₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ * J₀ *
      (X₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = J₀ := by
  apply Matrix.map_injective hφ
  change ((X₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ * J₀ *
      (X₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).map (algebraMap F K) =
    J₀.map (algebraMap F K)
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hJ, hX, h]

private lemma ggJSt3_conj_gram {n : ℕ} {K : Type} [Field K]
    (P g : GL (Fin n ⊕ Fin n) K) (J' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (hJ' : J' = ((P⁻¹ : GL (Fin n ⊕ Fin n) K) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
      ((P⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))
    (h : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) :
    ((P * g * P⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
      J' * ((P * g * P⁻¹ : GL (Fin n ⊕ Fin n) K) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = J' := by
  rw [hJ']
  set J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := fromBlocks 0 1 (-1) 0 with hJdef
  set Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    ((P⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) with hQ
  set Pm : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    (P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) with hPm
  have hcoe : ((P * g * P⁻¹ : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Pm * (g : Matrix _ _ K) * Q := by
    rw [hPm, hQ]
    simp only [Units.val_mul]
  rw [hcoe]
  have hQP : Q * Pm = 1 := by
    rw [hQ, hPm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 : Pmᵀ * Qᵀ = 1 := by
    rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one]
  have hL : (Pm * (g : Matrix _ _ K) * Q)ᵀ * (Qᵀ * J * Q) * (Pm * (g : Matrix _ _ K) * Q)
      = Qᵀ * ((g : Matrix _ _ K)ᵀ * J * (g : Matrix _ _ K)) * Q := by
    calc (Pm * (g : Matrix _ _ K) * Q)ᵀ * (Qᵀ * J * Q) * (Pm * (g : Matrix _ _ K) * Q)
        = Qᵀ * (g : Matrix _ _ K)ᵀ * (Pmᵀ * Qᵀ) * J * (Q * Pm) *
            (g : Matrix _ _ K) * Q := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul]
          noncomm_ring
      _ = Qᵀ * (g : Matrix _ _ K)ᵀ * J * (g : Matrix _ _ K) * Q := by
          rw [h1, hQP]
          simp only [Matrix.mul_one, Matrix.one_mul]
      _ = Qᵀ * ((g : Matrix _ _ K)ᵀ * J * (g : Matrix _ _ K)) * Q := by noncomm_ring
  rw [hL, h]

private lemma ggJSt3_conj_gram_C {n : ℕ} {F : Type} [Field F]
    (C X : GL (Fin n ⊕ Fin n) F) (J₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (hC : (C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ * J₀ *
      (C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))
    (hX : (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ * J₀ *
      (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = J₀) :
    (((C⁻¹ * X * C : GL (Fin n ⊕ Fin n) F)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ *
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (((C⁻¹ * X * C : GL (Fin n ⊕ Fin n) F)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
  have hJ : (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ * J₀ *
        (C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := hC.symm
  rw [hJ]
  set Cm : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    (C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) with hCm
  set Ci : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    ((C⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) with hCi
  have hcoe : ((C⁻¹ * X * C : GL (Fin n ⊕ Fin n) F) : Matrix _ _ F) =
      Ci * (X : Matrix _ _ F) * Cm := by
    rw [hCm, hCi]
    simp only [Units.val_mul]
  rw [hcoe]
  have hCmCi : Cm * Ci = 1 := by
    rw [hCm, hCi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : Ciᵀ * Cmᵀ = 1 := by rw [← Matrix.transpose_mul, hCmCi, Matrix.transpose_one]
  have hL : (Ci * (X : Matrix _ _ F) * Cm)ᵀ * (Cmᵀ * J₀ * Cm) * (Ci * (X : Matrix _ _ F) * Cm)
      = Cmᵀ * ((X : Matrix _ _ F)ᵀ * J₀ * (X : Matrix _ _ F)) * Cm := by
    calc (Ci * (X : Matrix _ _ F) * Cm)ᵀ * (Cmᵀ * J₀ * Cm) *
          (Ci * (X : Matrix _ _ F) * Cm)
        = Cmᵀ * (X : Matrix _ _ F)ᵀ * (Ciᵀ * Cmᵀ) * J₀ * (Cm * Ci) *
            (X : Matrix _ _ F) * Cm := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul]
          noncomm_ring
      _ = Cmᵀ * (X : Matrix _ _ F)ᵀ * J₀ * (X : Matrix _ _ F) * Cm := by
          rw [h1, hCmCi]
          simp only [Matrix.mul_one, Matrix.one_mul]
      _ = Cmᵀ * ((X : Matrix _ _ F)ᵀ * J₀ * (X : Matrix _ _ F)) * Cm := by noncomm_ring
  rw [hL, hX]

private lemma ggJSt3_isAlt_fromBlocks {n : ℕ} {F : Type} [Field F] [CharP F 2] :
    (Matrix.toBilin' (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).IsAlt := by
  intro x
  rw [Matrix.toBilin'_apply']
  have hneg : (-1 : Matrix (Fin n) (Fin n) F) = 1 := by
    ext i j
    simp [Matrix.neg_apply, CharTwo.neg_eq]
  have hJv : (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ x =
      Sum.elim (fun i => x (Sum.inr i)) (fun i => x (Sum.inl i)) := by
    rw [Matrix.fromBlocks_mulVec, hneg]
    ext i
    rcases i with i | i <;> simp
  rw [hJv, dotProduct, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hcomm : (∑ i, x (Sum.inl i) * x (Sum.inr i)) =
      ∑ i, x (Sum.inr i) * x (Sum.inl i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  rw [hcomm]
  exact CharTwo.add_self_eq_zero _

private lemma ggJSt3_isAlt_conjJ {n : ℕ} {K : Type} [Field K] [CharP K 2]
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    (Matrix.toBilin' (Qᵀ * (fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * Q)).IsAlt := by
  intro x
  rw [Matrix.toBilin'_apply']
  have hx := ggJSt3_isAlt_fromBlocks (n := n) (F := K) (Q *ᵥ x)
  rw [Matrix.toBilin'_apply'] at hx
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  exact hx

private lemma ggJSt3_isAlt_of_map {n : ℕ} {F K : Type} [Field F] [Field K] [Algebra F K]
    (hφ : Function.Injective (algebraMap F K))
    (J₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (J' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (h : J₀.map (algebraMap F K) = J')
    (halt : (Matrix.toBilin' J').IsAlt) : (Matrix.toBilin' J₀).IsAlt := by
  intro x
  rw [Matrix.toBilin'_apply']
  set xK : Fin n ⊕ Fin n → K := fun i => algebraMap F K (x i) with hxK
  have hx := halt xK
  rw [Matrix.toBilin'_apply'] at hx
  apply hφ
  rw [map_zero, RingHom.map_dotProduct]
  have h1 : ((algebraMap F K) ∘ x) = xK := rfl
  have h2 : ((algebraMap F K) ∘ (J₀ *ᵥ x)) = J' *ᵥ xK := by
    ext i
    rw [Function.comp_apply, RingHom.map_mulVec, h]
    rfl
  rw [h1, h2]
  exact hx

private lemma ggJSt3_isUnit_det_conjJ {n : ℕ} {K : Type} [Field K] [CharP K 2]
    (P : GL (Fin n ⊕ Fin n) K) :
    IsUnit ((((P⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
      ((P⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))).det := by
  have hJdet : IsUnit (fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).det := by
    rw [← ggJSt3_J_eq_fromBlocks]
    exact Matrix.isUnit_det_J (Fin n) K
  have hQdet : IsUnit (((P⁻¹ : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).det) :=
    isUnit_iff_ne_zero.mpr (Matrix.GeneralLinearGroup.det_ne_zero (P⁻¹))
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_assoc]
  exact hQdet.mul (hJdet.mul hQdet)

private lemma ggJSt3_statedSp_eq_gramIsometry {n : ℕ} {K : Type} [Field K] :
    StatedSp n K = gramIsometry (fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
  rw [StatedSp]
  exact Subgroup.closure_eq (gramIsometry _)

private lemma ggJSt3_cast_orderOf_ne_zero {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (h : Odd n) : (n : AlgebraicClosure K) ≠ 0 := by
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  intro h0
  have h2 : (2 : ℕ) ∣ n := (CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 n).mp h0
  exact (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr h2)

private lemma ggJSt3_map_gram {n : ℕ} {F K : Type} [Field F] [Field K] [Algebra F K]
    (J₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (J' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (hJ : J₀.map (algebraMap F K) = J')
    (X₀ : GL (Fin n ⊕ Fin n) F)
    (h : (X₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ * J₀ *
      (X₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = J₀) :
    ((X₀.map (algebraMap F K) : GL (Fin n ⊕ Fin n) K) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * J' *
      ((X₀.map (algebraMap F K) : GL (Fin n ⊕ Fin n) K) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = J' := by
  have hh := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F =>
    M.map (algebraMap F K)) h
  simpa only [Matrix.GeneralLinearGroup.val_map_apply, Matrix.map_mul, Matrix.map_mul,
    Matrix.transpose_map, hJ] using hh

private lemma ggJSt3_conj_gram_C_inv {n : ℕ} {F : Type} [Field F]
    (C X : GL (Fin n ⊕ Fin n) F) (J₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (hC : (C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ * J₀ *
      (C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))
    (hX : (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ *
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) :
    (((C * X * C⁻¹ : GL (Fin n ⊕ Fin n) F)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ * J₀ *
      (((C * X * C⁻¹ : GL (Fin n ⊕ Fin n) F)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = J₀ := by
  set Fm : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := fromBlocks 0 1 (-1) 0 with hFm
  set Cm : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    (C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) with hCm
  set Ci : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    ((C⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) with hCi
  have hCiCm : Ci * Cm = 1 := by
    rw [hCi, hCm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hCmCi : Cm * Ci = 1 := by
    rw [hCm, hCi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hJ₀ : J₀ = Ciᵀ * Fm * Ci := by
    rw [show Fm = Cmᵀ * J₀ * Cm from hC.symm]
    symm
    calc Ciᵀ * (Cmᵀ * J₀ * Cm) * Ci = (Cm * Ci)ᵀ * J₀ * (Cm * Ci) := by
          rw [Matrix.transpose_mul]
          noncomm_ring
      _ = J₀ := by
          rw [hCmCi]
          simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hcoe : ((C * X * C⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix _ _ F) =
      Cm * (X : Matrix _ _ F) * Ci := by
    rw [hCm, hCi]
    simp only [Units.val_mul]
  rw [hJ₀, hcoe]
  have h1 : Cmᵀ * Ciᵀ = 1 := by rw [← Matrix.transpose_mul, hCiCm, Matrix.transpose_one]
  have hL : (Cm * (X : Matrix _ _ F) * Ci)ᵀ * (Ciᵀ * Fm * Ci) *
        (Cm * (X : Matrix _ _ F) * Ci)
      = Ciᵀ * ((X : Matrix _ _ F)ᵀ * Fm * (X : Matrix _ _ F)) * Ci := by
    calc (Cm * (X : Matrix _ _ F) * Ci)ᵀ * (Ciᵀ * Fm * Ci) *
          (Cm * (X : Matrix _ _ F) * Ci)
        = Ciᵀ * (X : Matrix _ _ F)ᵀ * (Cmᵀ * Ciᵀ) * Fm * (Ci * Cm) *
            (X : Matrix _ _ F) * Ci := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul]
          noncomm_ring
      _ = Ciᵀ * (X : Matrix _ _ F)ᵀ * Fm * (X : Matrix _ _ F) * Ci := by
          rw [h1, hCiCm]
          simp only [Matrix.mul_one, Matrix.one_mul]
      _ = Ciᵀ * ((X : Matrix _ _ F)ᵀ * Fm * (X : Matrix _ _ F)) * Ci := by noncomm_ring
  rw [hL, hX]

private lemma ggJSt3_conj_P_inv_gram {n : ℕ} {K : Type} [Field K]
    (P x : GL (Fin n ⊕ Fin n) K) (J' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (hJ' : J' = ((P⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
      ((P⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))
    (h : (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * J' *
      (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = J') :
    ((P⁻¹ * x * P : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
      ((P⁻¹ * x * P : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
  set F : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := fromBlocks 0 1 (-1) 0 with hF
  set Pm : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    (P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) with hPm
  set Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    ((P⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) with hQ
  have hPQ : Pm * Q = 1 := by
    rw [hPm, hQ, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQP : Q * Pm = 1 := by
    rw [hQ, hPm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hF' : F = Pmᵀ * J' * Pm := by
    rw [show J' = Qᵀ * F * Q from hJ']
    have h1 : Pmᵀ * Qᵀ = 1 := by rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one]
    calc F = (Pmᵀ * Qᵀ) * F * (Q * Pm) := by
          rw [h1, hQP]
          simp only [Matrix.one_mul, Matrix.mul_one]
      _ = Pmᵀ * (Qᵀ * F * Q) * Pm := by noncomm_ring
  rw [hF']
  have hcoe : ((P⁻¹ * x * P : GL (Fin n ⊕ Fin n) K) : Matrix _ _ K) =
      Q * (x : Matrix _ _ K) * Pm := by
    rw [hPm, hQ]
    simp only [Units.val_mul]
  rw [hcoe]
  have h1 : Qᵀ * Pmᵀ = 1 := by rw [← Matrix.transpose_mul, hPQ, Matrix.transpose_one]
  have hL : (Q * (x : Matrix _ _ K) * Pm)ᵀ * (Pmᵀ * J' * Pm) * (Q * (x : Matrix _ _ K) * Pm)
      = Pmᵀ * ((x : Matrix _ _ K)ᵀ * J' * (x : Matrix _ _ K)) * Pm := by
    calc (Q * (x : Matrix _ _ K) * Pm)ᵀ * (Pmᵀ * J' * Pm) * (Q * (x : Matrix _ _ K) * Pm)
        = Pmᵀ * (x : Matrix _ _ K)ᵀ * (Qᵀ * Pmᵀ) * J' * (Pm * Q) *
            (x : Matrix _ _ K) * Pm := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul]
          noncomm_ring
      _ = Pmᵀ * (x : Matrix _ _ K)ᵀ * J' * (x : Matrix _ _ K) * Pm := by
          rw [h1, hPQ]
          simp only [Matrix.mul_one, Matrix.one_mul]
      _ = Pmᵀ * ((x : Matrix _ _ K)ᵀ * J' * (x : Matrix _ _ K)) * Pm := by noncomm_ring
  rw [hL, h]

theorem descent_centralizer_Sp {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (σ : K ≃+* K) (hσ : σ ≠ RingEquiv.refl K) (hσ2 : ∀ x, σ (σ x) = x)
    (A : GL (Fin n ⊕ Fin n) K) (hA : A ∈ StatedSp n K) (hAA : A * A.map σ.toRingHom = 1)
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    (hfix : ∀ g ∈ (Subgroup.centralizer {b}).comap (StatedSp n K).subtype,
      A * (g : GL (Fin n ⊕ Fin n) K).map σ.toRingHom * A⁻¹ = g) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : Fintype K₀) (_ : CharP K₀ 2)
      (b₀ : GL (Fin n ⊕ Fin n) K₀), b₀ ∈ StatedSp n K₀ ∧ Odd (orderOf b₀) ∧
      Fintype.card K = Fintype.card K₀ ^ 2 ∧
      Nonempty (↥((Subgroup.centralizer {b}).comap (StatedSp n K).subtype) ≃*
        ↥((Subgroup.centralizer {b₀}).comap (StatedSp n K₀).subtype)) ∧
      blockExp false (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        blockExp false (b₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K₀) := by
  classical
  haveI : Finite K := Finite.of_fintype K
  obtain ⟨P, hP⟩ := ggJSt3_hilbert90 σ hσ hσ2 A hAA
  let J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := fromBlocks 0 1 (-1) 0
  let Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    ((P⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
  let J' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := Qᵀ * J * Q
  have hAJ : (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * J *
      (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = J := by
    simpa [J] using (mem_statedSp_iff).mp hA
  have hJ'map : J'.map σ = J' := by
    have h := ggJSt3_form_fixed σ P A (by simpa [J] using hAJ) hP
    simpa [J, Q, J'] using h
  let K₀ : Subfield K := fixedField K σ
  haveI : Fintype ↥K₀ := Fintype.ofFinite ↥K₀
  let J₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥K₀ :=
    ggJSt3_descendMatrix σ J' (fun i j => congrFun (congrFun hJ'map i) j)
  have hJ₀map : J₀.map (algebraMap ↥K₀ K) = J' := ggJSt3_descendMatrix_map σ J' _
  have hφinj : Function.Injective (algebraMap ↥K₀ K) := (algebraMap ↥K₀ K).injective
  have hJ'det : IsUnit J'.det := by
    have h := ggJSt3_isUnit_det_conjJ P
    simpa [J, Q, J'] using h
  have hJ₀Alt : (Matrix.toBilin' J₀).IsAlt :=
    ggJSt3_isAlt_of_map hφinj J₀ J' hJ₀map (by
      have h := ggJSt3_isAlt_conjJ Q
      simpa [J, J'] using h)
  have hJ₀Non : (Matrix.toBilin' J₀).Nondegenerate := by
    refine LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' J₀ ?_
    intro h0
    apply hJ'det.ne_zero
    rw [← hJ₀map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  obtain ⟨C, hC⟩ := ggJSt3_exists_symplectic J₀ hJ₀Alt hJ₀Non
  have hfixb : A * (b : GL (Fin n ⊕ Fin n) K).map σ.toRingHom * A⁻¹ = b :=
    hfix ⟨b, hb⟩ (by
      rw [Subgroup.mem_comap]
      exact Subgroup.mem_centralizer_iff.mpr (fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        subst hx
        rfl))
  have hb''fix : (P * b * P⁻¹).map σ.toRingHom = P * b * P⁻¹ :=
    ggJSt3_conj_fixed_of_hfix σ A P b hP hfixb
  let b'' : GL (Fin n ⊕ Fin n) K := P * b * P⁻¹
  let b' : GL (Fin n ⊕ Fin n) ↥K₀ := ggJSt3_descendGL σ b'' hb''fix
  have hb'map : b'.map (algebraMap ↥K₀ K) = b'' := ggJSt3_descendGL_map σ b'' hb''fix
  have hb'mapM : (b' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥K₀).map (algebraMap ↥K₀ K) =
      (b'' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
    have h := congrArg (fun X : GL (Fin n ⊕ Fin n) K =>
      (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hb'map
    simpa [Matrix.GeneralLinearGroup.val_map_apply] using h
  have hbJ : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * J *
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = J := by
    simpa [J] using (mem_statedSp_iff).mp hb
  have hb''J : (b'' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * J' *
      (b'' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = J' :=
    ggJSt3_conj_gram P b J' rfl hbJ
  have hb'J : (b' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥K₀)ᵀ * J₀ *
      (b' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥K₀) = J₀ :=
    ggJSt3_descend_gram hφinj J₀ J' hJ₀map b' b'' hb'mapM hb''J
  let b₀ : GL (Fin n ⊕ Fin n) ↥K₀ := C⁻¹ * b' * C
  have hb₀J : (b₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥K₀)ᵀ *
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥K₀) *
      (b₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥K₀) =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥K₀) :=
    ggJSt3_conj_gram_C C b' J₀ hC hb'J
  have hb₀mem : b₀ ∈ StatedSp n ↥K₀ := (mem_statedSp_iff).mpr hb₀J
  have hcard : Fintype.card K = Fintype.card ↥K₀ ^ 2 := by
    have h := card_eq_fixedField_card_sq K σ (ggJSt3_orderOf_sigma σ hσ hσ2)
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  have horder_b'' : orderOf b'' = orderOf b := by
    apply Nat.dvd_antisymm
    · rw [orderOf_dvd_iff_pow_eq_one]
      have h : b'' = MulAut.conj P b := by
        rw [show b'' = P * b * P⁻¹ from rfl, MulAut.conj_apply]
      rw [h, ← map_pow, pow_orderOf_eq_one, map_one]
    · rw [orderOf_dvd_iff_pow_eq_one]
      have h : b = MulAut.conj P⁻¹ b'' := by
        rw [show b'' = P * b * P⁻¹ from rfl, MulAut.conj_apply]
        group
      rw [h, ← map_pow, pow_orderOf_eq_one, map_one]
  have horder_b' : orderOf b' = orderOf b'' := by
    apply Nat.dvd_antisymm
    · rw [orderOf_dvd_iff_pow_eq_one]
      apply (Matrix.GeneralLinearGroup.map_injective (f := algebraMap ↥K₀ K) hφinj)
      rw [map_pow, hb'map, pow_orderOf_eq_one, map_one]
    · rw [orderOf_dvd_iff_pow_eq_one]
      rw [← hb'map, ← map_pow, pow_orderOf_eq_one, map_one]
  have horder_b₀ : orderOf b₀ = orderOf b' := by
    apply Nat.dvd_antisymm
    · rw [orderOf_dvd_iff_pow_eq_one]
      have h : b₀ = MulAut.conj C⁻¹ b' := by
        rw [show b₀ = C⁻¹ * b' * C from rfl, MulAut.conj_apply, inv_inv]
      rw [h, ← map_pow, pow_orderOf_eq_one, map_one]
    · rw [orderOf_dvd_iff_pow_eq_one]
      have h : b' = MulAut.conj C b₀ := by
        rw [show b₀ = C⁻¹ * b' * C from rfl, MulAut.conj_apply]
        group
      rw [h, ← map_pow, pow_orderOf_eq_one, map_one]
  have hodd_b'' : Odd (orderOf b'') := by rw [horder_b'']; exact hodd
  have hodd_b' : Odd (orderOf b') := by rw [horder_b']; exact hodd_b''
  have hodd_b₀ : Odd (orderOf b₀) := by
    rw [horder_b₀, horder_b', horder_b'']
    exact hodd
  refine ⟨↥K₀, inferInstance, inferInstance, inferInstance, b₀, hb₀mem, hodd_b₀, hcard, ?_, ?_⟩
  · let H_K : Subgroup ↥(StatedSp n K) :=
      (Subgroup.centralizer {b}).comap (StatedSp n K).subtype
    let H_F : Subgroup ↥(StatedSp n ↥K₀) :=
      (Subgroup.centralizer {b₀}).comap (StatedSp n ↥K₀).subtype
    let HK : Subgroup (GL (Fin n ⊕ Fin n) K) := H_K.map (StatedSp n K).subtype
    let HF : Subgroup (GL (Fin n ⊕ Fin n) ↥K₀) := H_F.map (StatedSp n ↥K₀).subtype
    let Fix : Subgroup (GL (Fin n ⊕ Fin n) K) := ggJSt3_fixedSubgroup (ι := Fin n ⊕ Fin n) σ
    let H'' : Subgroup (GL (Fin n ⊕ Fin n) K) :=
      gramIsometry J' ⊓ Subgroup.centralizer {b''}
    let Hdom : Subgroup ↥Fix := H''.subgroupOf Fix
    let H0 : Subgroup (GL (Fin n ⊕ Fin n) ↥K₀) :=
      gramIsometry J₀ ⊓ Subgroup.centralizer {b'}
    change Nonempty (↥H_K ≃* ↥H_F)
    have hHK : HK = gramIsometry (fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ⊓ Subgroup.centralizer {b} := by
      rw [show HK = Subgroup.map (StatedSp n K).subtype
          (Subgroup.comap (StatedSp n K).subtype (Subgroup.centralizer {b})) from rfl,
        Subgroup.map_comap_eq, Subgroup.range_subtype,
        ggJSt3_statedSp_eq_gramIsometry (n := n) (K := K)]
    have hHKleFix : HK.map (MulAut.conj P).toMonoidHom ≤ Fix := by
      intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Subgroup.mem_map] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      change (P * (g : GL (Fin n ⊕ Fin n) K) * P⁻¹).map σ = P * (g : GL (Fin n ⊕ Fin n) K) * P⁻¹
      exact ggJSt3_conj_fixed_of_hfix σ A P (g : GL (Fin n ⊕ Fin n) K) hP (hfix g hg)
    have hA : HK.map (MulAut.conj P).toMonoidHom = H'' := by
      rw [hHK]
      apply le_antisymm
      · intro x hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [Subgroup.mem_inf] at hy ⊢
        obtain ⟨hyJ, hyC⟩ := hy
        constructor
        · exact ggJSt3_conj_gram P y J' (by simp [J, Q, J']) hyJ
        · rw [Subgroup.mem_centralizer_iff] at hyC ⊢
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          subst hz
          have hyb : b * y = y * b := hyC b (Set.mem_singleton b)
          calc b'' * (MulAut.conj P y) = P * (b * y) * P⁻¹ := by
                rw [show b'' = P * b * P⁻¹ from rfl, MulAut.conj_apply]; group
            _ = P * (y * b) * P⁻¹ := by rw [hyb]
            _ = (MulAut.conj P y) * b'' := by
                rw [show b'' = P * b * P⁻¹ from rfl, MulAut.conj_apply]; group
      · intro x hx
        rw [Subgroup.mem_inf] at hx
        obtain ⟨hxJ, hxC⟩ := hx
        rw [Subgroup.mem_map]
        refine ⟨(MulAut.conj P).symm x, ?_, ?_⟩
        · rw [Subgroup.mem_inf]
          constructor
          · exact ggJSt3_conj_P_inv_gram P x J' (by simp [J, Q, J']) hxJ
          · rw [Subgroup.mem_centralizer_iff] at hxC ⊢
            intro z hz
            rw [Set.mem_singleton_iff] at hz
            subst z
            have hx' : b'' * x = x * b'' := hxC b'' (Set.mem_singleton b'')
            rw [MulAut.conj_symm_apply]
            calc b * (P⁻¹ * x * P) = P⁻¹ * (b'' * x) * P := by
                  rw [show b'' = P * b * P⁻¹ from rfl]; group
              _ = P⁻¹ * (x * b'') * P := by rw [hx']
              _ = (P⁻¹ * x * P) * b := by
                  rw [show b'' = P * b * P⁻¹ from rfl]; group
        · exact (MulAut.conj P).apply_symm_apply x
    have hH''leFix : H'' ≤ Fix := hA ▸ hHKleFix
    have hdom : HK.map (MulAut.conj P).toMonoidHom = Hdom.map Fix.subtype := by
      rw [Subgroup.map_subgroupOf_eq_of_le hH''leFix]
      exact hA
    have hB : Hdom.map (ggJSt3_fixedGL_equiv (ι := Fin n ⊕ Fin n) σ).toMonoidHom = H0 := by
      apply le_antisymm
      · intro x hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [Subgroup.mem_subgroupOf] at hy
        rw [Subgroup.mem_inf] at hy ⊢
        obtain ⟨hyJ, hyC⟩ := hy
        have hyval : ((ggJSt3_fixedGL_equiv (ι := Fin n ⊕ Fin n) σ y) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥K₀).map (algebraMap ↥K₀ K) =
            (y.val : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
          change (↑(ggJSt3_descendGL σ (y.val : GL (Fin n ⊕ Fin n) K) y.property) :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥K₀).map (algebraMap ↥K₀ K) =
            ↑(y.val : GL (Fin n ⊕ Fin n) K)
          rw [← Matrix.GeneralLinearGroup.val_map_apply,
            ggJSt3_descendGL_map σ (y.val : GL (Fin n ⊕ Fin n) K) y.property]
        have hxmap : Matrix.GeneralLinearGroup.map (algebraMap ↥K₀ K)
            ((ggJSt3_fixedGL_equiv (ι := Fin n ⊕ Fin n) σ).toMonoidHom y) =
            (y.val : GL (Fin n ⊕ Fin n) K) := by
          apply Units.ext
          rw [Matrix.GeneralLinearGroup.val_map_apply]
          exact hyval
        constructor
        · exact ggJSt3_descend_gram hφinj J₀ J' hJ₀map
            (ggJSt3_fixedGL_equiv (ι := Fin n ⊕ Fin n) σ y) y.val hyval hyJ
        · rw [Subgroup.mem_centralizer_iff] at hyC ⊢
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          subst hz
          apply (Matrix.GeneralLinearGroup.map_injective (f := algebraMap ↥K₀ K) hφinj)
          rw [map_mul, map_mul, hxmap, hb'map]
          exact hyC b'' (Set.mem_singleton b'')
      · intro x hx
        rw [Subgroup.mem_inf] at hx
        obtain ⟨hxJ, hxC⟩ := hx
        rw [Subgroup.mem_map]
        refine ⟨(ggJSt3_fixedGL_equiv (ι := Fin n ⊕ Fin n) σ).symm x, ?_, ?_⟩
        · rw [Subgroup.mem_subgroupOf]
          rw [Subgroup.mem_inf]
          have hyval : ((ggJSt3_fixedGL_equiv (ι := Fin n ⊕ Fin n) σ).symm x).val =
              x.map (algebraMap ↥K₀ K) := by
            have h := ggJSt3_descendGL_map σ
              ((ggJSt3_fixedGL_equiv (ι := Fin n ⊕ Fin n) σ).symm x).val
              ((ggJSt3_fixedGL_equiv (ι := Fin n ⊕ Fin n) σ).symm x).property
            change (ggJSt3_fixedGL_equiv (ι := Fin n ⊕ Fin n) σ
              ((ggJSt3_fixedGL_equiv (ι := Fin n ⊕ Fin n) σ).symm x)).map (algebraMap ↥K₀ K) =
              ((ggJSt3_fixedGL_equiv (ι := Fin n ⊕ Fin n) σ).symm x).val at h
            rw [MulEquiv.apply_symm_apply] at h
            exact h.symm
          constructor
          · have hmap := ggJSt3_map_gram J₀ J' hJ₀map x hxJ
            change (((↑((ggJSt3_fixedGL_equiv (ι := Fin n ⊕ Fin n) σ).symm x)) :
                GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * J' *
                (((↑((ggJSt3_fixedGL_equiv (ι := Fin n ⊕ Fin n) σ).symm x)) :
                GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = J'
            rw [hyval]
            exact hmap
          · rw [Subgroup.mem_centralizer_iff] at hxC ⊢
            intro z hz
            rw [Set.mem_singleton_iff] at hz
            subst hz
            have hx' : b' * x = x * b' := hxC b' (Set.mem_singleton b')
            have hconj := congrArg (fun w : GL (Fin n ⊕ Fin n) ↥K₀ =>
              Matrix.GeneralLinearGroup.map (algebraMap ↥K₀ K) w) hx'
            simpa only [map_mul, hyval, hb'map] using hconj
        · exact (ggJSt3_fixedGL_equiv (ι := Fin n ⊕ Fin n) σ).apply_symm_apply x
    have hC : H0.map (MulAut.conj C⁻¹).toMonoidHom = HF := by
      have hHF : HF = gramIsometry (fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥K₀) ⊓ Subgroup.centralizer {b₀} := by
        rw [show HF = Subgroup.map (StatedSp n ↥K₀).subtype
            (Subgroup.comap (StatedSp n ↥K₀).subtype (Subgroup.centralizer {b₀})) from rfl,
          Subgroup.map_comap_eq, Subgroup.range_subtype,
          ggJSt3_statedSp_eq_gramIsometry (n := n) (K := ↥K₀)]
      rw [hHF]
      apply le_antisymm
      · intro x hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [Subgroup.mem_inf] at hy ⊢
        obtain ⟨hyJ, hyC⟩ := hy
        constructor
        · exact ggJSt3_conj_gram_C C y J₀ hC hyJ
        · rw [Subgroup.mem_centralizer_iff] at hyC ⊢
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          subst hz
          have hyb : b' * y = y * b' := hyC b' (Set.mem_singleton b')
          have hconj : C⁻¹ * (b' * y) * C = C⁻¹ * (y * b') * C :=
            congrArg (fun w => C⁻¹ * w * C) hyb
          calc b₀ * (MulAut.conj C⁻¹ y) = C⁻¹ * (b' * y) * C := by
                rw [show b₀ = C⁻¹ * b' * C from rfl, MulAut.conj_apply]; group
            _ = C⁻¹ * (y * b') * C := hconj
            _ = (MulAut.conj C⁻¹ y) * b₀ := by
                rw [show b₀ = C⁻¹ * b' * C from rfl, MulAut.conj_apply]; group
      · intro x hx
        rw [Subgroup.mem_inf] at hx
        obtain ⟨hxJ, hxC⟩ := hx
        rw [Subgroup.mem_map]
        refine ⟨(MulAut.conj C⁻¹).symm x, ?_, ?_⟩
        · rw [Subgroup.mem_inf]
          constructor
          · exact ggJSt3_conj_gram_C_inv C x J₀ hC hxJ
          · rw [Subgroup.mem_centralizer_iff] at hxC ⊢
            intro z hz
            rw [Set.mem_singleton_iff] at hz
            subst hz
            have hx' : b₀ * x = x * b₀ := hxC b₀ (Set.mem_singleton b₀)
            have hconj : C * (b₀ * x) * C⁻¹ = C * (x * b₀) * C⁻¹ :=
              congrArg (fun w => C * w * C⁻¹) hx'
            calc b' * ((MulAut.conj C⁻¹).symm x) = C * (b₀ * x) * C⁻¹ := by
                  rw [MulAut.conj_symm_apply, show b₀ = C⁻¹ * b' * C from rfl]; group
              _ = C * (x * b₀) * C⁻¹ := hconj
              _ = ((MulAut.conj C⁻¹).symm x) * b' := by
                  rw [MulAut.conj_symm_apply, show b₀ = C⁻¹ * b' * C from rfl]; group
        · exact (MulAut.conj C⁻¹).apply_symm_apply x
    exact ⟨((Subgroup.equivMapOfInjective H_K (StatedSp n K).subtype
        (Subgroup.subtype_injective _)).trans
      (((MulAut.conj P).subgroupMap HK).trans
        ((MulEquiv.subgroupCongr hdom).trans
          (((Subgroup.equivMapOfInjective Hdom Fix.subtype
              (Subgroup.subtype_injective _)).symm).trans
            (((ggJSt3_fixedGL_equiv (ι := Fin n ⊕ Fin n) σ).subgroupMap Hdom).trans
              ((MulEquiv.subgroupCongr hB).trans
                (((MulAut.conj C⁻¹).subgroupMap H0).trans
                  ((MulEquiv.subgroupCongr hC).trans
                    ((Subgroup.equivMapOfInjective H_F (StatedSp n ↥K₀).subtype
                      (Subgroup.subtype_injective _)).symm)))))))))⟩
  · have h1 : blockExp false (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        blockExp false (b'' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
      rw [show b'' = P * b * P⁻¹ from rfl]
      exact (ggJSt3_blockExp_conj P b (orderOf b)
        (ggJSt3_cast_orderOf_ne_zero hodd) (pow_orderOf_eq_one b)).symm
    have h2 : blockExp false (b'' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        blockExp false (b' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥K₀) := by
      have hb'pow : (b' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥K₀) ^ orderOf b' = 1 := by
        rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
      have hmap := ggJSt3_blockExp_map (ι := Fin n ⊕ Fin n) (F := ↥K₀) (K := K)
        (b' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥K₀) (orderOf b')
        (ggJSt3_cast_orderOf_ne_zero (K := ↥K₀) hodd_b') hb'pow
      rw [show b'' = b'.map (algebraMap ↥K₀ K) from hb'map.symm]
      simpa [Matrix.GeneralLinearGroup.val_map_apply] using hmap
    have h3 : blockExp false (b' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥K₀) =
        blockExp false (b₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ↥K₀) :=
      (ggJSt3_blockExp_conj C⁻¹ b' (orderOf b')
        (ggJSt3_cast_orderOf_ne_zero hodd_b') (pow_orderOf_eq_one b')).symm
    exact h1.trans (h2.trans h3)

end CFSG.StandardType.ClassicalBlocks
