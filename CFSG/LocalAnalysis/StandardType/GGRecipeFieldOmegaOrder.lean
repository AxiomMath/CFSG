module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaConj

public section

namespace CFSG.StandardType

namespace RecipeFieldOmega

section Lang

open CFSG.Assembly CFSG.GroupTheory.WeirSylow QuadraticMap
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField

variable {K : Type} [Field K] {d : ℕ}

theorem exists_fixed_basis_pair_of_pos [Finite K] {σ : K ≃+* K} {p : ℕ} (hp : 0 < p)
    (hσ : orderOf σ = p) {X : coordinateSemilinearGroup d K} (hXr : X.right = σ)
    (hXp : X ^ p = 1) : ∃ H : GL (Fin d) K, X.left * glFieldAut (Fin d) K σ H = H := by
  let T : (Fin d → K) →+ (Fin d → K) := (coordinateSemilinearMap X).toAddMonoidHom
  have hsmul : ∀ (a : K) (v : Fin d → K), T (a • v) = σ a • T v := fun a v => by
    change coordinateSemilinearMap X (a • v) = σ a • coordinateSemilinearMap X v
    rw [coordinateSemilinearMap_smul, hXr]
  have hTp : ∀ v, T^[p] v = v := fun v => by
    change (coordinateSemilinearMap X)^[p] v = v
    rw [coordinateSemilinearMap_iterate, hXp, coordinateSemilinearMap_one]
  obtain ⟨θ, hθ⟩ := exists_moved hσ
  obtain ⟨H, hH⟩ := RecipeFieldLang.exists_fixed_basis_of_span T
    (RecipeFieldLang.span_fixed_eq_top T hsmul hp hTp hθ)
  refine ⟨H, ?_⟩
  ext r c
  have h := congrFun (hH c) r
  change coordinateSemilinearMap X (fun r => (H : Matrix (Fin d) (Fin d) K) r c) r = _ at h
  rw [coordinateSemilinearMap_apply, hXr] at h
  simp only [Matrix.mulVec, dotProduct] at h
  rw [← h]
  simp [Matrix.mul_apply, glFieldAut_apply_val]

theorem exists_isometry_conj_of_isIsoPair_odd [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hnd : (polarBilin Q).Nondegenerate) {p : ℕ}
    (hpodd : Odd p) {S T : coordinateSemilinearGroup (2 * n) K}
    (hS : IsIsoPair Q S) (hT : IsIsoPair Q T) (hST : T.right = S.right)
    (hσ : orderOf S.right = p) (hSp : S ^ p = 1) (hTp : T ^ p = 1) :
    ∃ h : GL (Fin (2 * n)) K, h ∈ matrixIsometries Q ∧
      h * T.left = S.left * glFieldAut (Fin (2 * n)) K S.right h := by
  set σ := S.right with hσdef
  set K₀ : Subfield K := (σ : K →+* K).eqLocusField (RingHom.id K)
  have hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x := fun x => Iff.rfl
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hp0 : 0 < p := hpodd.pos
  obtain ⟨HS, hHS⟩ := exists_fixed_basis_pair_of_pos hp0 hσ rfl hSp
  obtain ⟨HT, hHT⟩ := exists_fixed_basis_pair_of_pos hp0 hσ hST hTp
  have hQS := mem_fixed_of_isIsoPair hS rfl hK₀ hHS
  have hQT := mem_fixed_of_isIsoPair hT hST hK₀ hHT
  have hndS := nondegenerate_comp_GL hnd HS
  have hndT := nondegenerate_comp_GL hnd HT
  have eS : (Q.comp (Matrix.toLin' HS.val)).IsometryEquiv Q := ⟨matrixLinearEquiv HS, fun _ => rfl⟩
  have eT : (Q.comp (Matrix.toLin' HT.val)).IsometryEquiv Q := ⟨matrixLinearEquiv HT, fun _ => rfl⟩
  have hiff : IsPlusType (descForm _ hQT) ↔ IsPlusType (descForm _ hQS) := by
    rw [isPlusType_descForm_iff hpodd hσp hK₀ hn hQT hndT,
      isPlusType_descForm_iff hpodd hσp hK₀ hn hQS hndS, isPlusType_congr eS, isPlusType_congr eT]
  obtain ⟨e⟩ := nonempty_isometry_of_isPlusType_iff (nondegenerate_descForm hQT hndT)
    (nondegenerate_descForm hQS hndS) (Module.finrank_fin_fun K₀) (Module.finrank_fin_fun K₀) hiff
  set M : GL (Fin (2 * n)) K₀ := matrixLinearIso.symm e.toLinearEquiv
  have hMw : ∀ w, M.val.mulVec w = e w := fun w => by
    change matrixLinearIso M w = e w
    rw [MulEquiv.apply_symm_apply]
    rfl
  set MK : GL (Fin (2 * n)) K := Matrix.GeneralLinearGroup.map K₀.subtype M
  have hMKw : ∀ w, MK.val.mulVec (inclVec K₀ w) = inclVec K₀ (e w) := fun w => by
    funext i
    have h1 := RingHom.map_mulVec K₀.subtype M.val w i
    rw [hMw] at h1
    exact h1.symm
  have hσM : glFieldAut (Fin (2 * n)) K σ MK = MK := by
    ext i j
    exact (hK₀ _).1 (M i j).2
  have hiso : (Q.comp (Matrix.toLin' HS.val)).comp (Matrix.toLin' MK.val) =
      Q.comp (Matrix.toLin' HT.val) := eq_of_forall_inclVec K₀ fun w => by
    rw [QuadraticMap.comp_apply, Matrix.toLin'_apply, hMKw, ← descForm_apply _ hQS, e.map_app,
      descForm_apply]
  refine ⟨HS * MK * HT⁻¹, ?_, ?_⟩
  · rw [mem_matrixIsometries_iff]
    intro v
    have h := congrArg (fun q : QuadraticForm K (Fin (2 * n) → K) =>
      q ((HT⁻¹ : GL (Fin (2 * n)) K).val.mulVec v)) hiso
    simp only [QuadraticMap.comp_apply, Matrix.toLin'_apply] at h
    rw [matrixLinearEquiv_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, h, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec]
  · have eTl : T.left = HT * (glFieldAut (Fin (2 * n)) K σ HT)⁻¹ := eq_mul_inv_of_mul_eq hHT
    have eSl : S.left = HS * (glFieldAut (Fin (2 * n)) K σ HS)⁻¹ := eq_mul_inv_of_mul_eq hHS
    rw [eTl, eSl, map_mul, map_mul, map_inv, hσM]
    group

end Lang

section Conj

open CFSG.Assembly QuadraticMap CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.RankThree.PartOne.AUTSL

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_conj_of_isIsoPair_odd {n : ℕ} (hn : 1 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hnd : Q.polarBilin.Nondegenerate)
    (hT3 : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hAP : CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.ActionProperties Q
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.projectivePointAction Q))
    {p : ℕ} (hpodd : Odd p) {S : similarityPairs Q} (hS : IsIsoPair Q S.val)
    (hσ : orderOf S.val.right = p)
    {w : Fin (2 * n) → K} (hw : Q w ≠ 0) (hSw : coordinateSemilinearMap S.val w = w)
    (γ : matrixDerived Q)
    (hord : (MulAut.conj γ * conjAct Q S) ^ p = 1) (hfp : conjAct Q S ^ p = 1) :
    ∃ u' ∈ inner (matrixDerived Q), MulAut.conj γ * conjAct Q S = u' * conjAct Q S * u'⁻¹ := by
  have hQne : ∃ v, Q v ≠ 0 := ⟨w, hw⟩
  have hγO : γ.val ∈ matrixIsometries Q := matrixDerived_le_isometries _ γ.2
  obtain ⟨T, hTdef⟩ : ∃ T : similarityPairs Q, T = matrixIsometryInclusion Q ⟨γ.val, hγO⟩ * S :=
    ⟨_, rfl⟩
  have hconjT : conjAct Q T = MulAut.conj γ * conjAct Q S := by
    rw [hTdef, map_mul, conjAct_inclusion_of_mem ⟨γ.val, hγO⟩ γ.2]
  have hTv : T.val = SemidirectProduct.inl γ.val * S.val := by
    rw [hTdef, Subgroup.coe_mul, matrixIsometryInclusion_val]
  have hT : IsIsoPair Q T.val := hTv ▸ (isIsoPair_inl hγO).mul hS
  have hTr : T.val.right = S.val.right := by
    rw [hTv, SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul]
  have hTp : T ^ p = 1 := eq_one_of_conjAct_eq_one hnd hT3 hAP hQne
    (by rw [SubmonoidClass.coe_pow]; exact hT.pow p) (by rw [map_pow, hconjT, hord])
  have hSp : S ^ p = 1 := eq_one_of_conjAct_eq_one hnd hT3 hAP hQne
    (by rw [SubmonoidClass.coe_pow]; exact hS.pow p) (by rw [map_pow, hfp])
  have hSpv : S.val ^ p = 1 := by rw [← SubmonoidClass.coe_pow, hSp]; rfl
  have hTpv : T.val ^ p = 1 := by rw [← SubmonoidClass.coe_pow, hTp]; rfl
  obtain ⟨h, hh, heq⟩ := exists_isometry_conj_of_isIsoPair_odd hn hnd hpodd hS hT hTr hσ hSpv hTpv
  obtain ⟨h', hh'Ω, heq'⟩ := exists_derived_conj hnd hT3 hS hw hSw hh heq
  have hh'O : h' ∈ matrixIsometries Q := matrixDerived_le_isometries _ hh'Ω
  have hpair : matrixIsometryInclusion Q ⟨h', hh'O⟩ * T =
      S * matrixIsometryInclusion Q ⟨h', hh'O⟩ := by
    apply Subtype.ext
    change SemidirectProduct.inl h' * T.val = S.val * SemidirectProduct.inl h'
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, map_one, MulAut.one_apply]
      exact heq'
    · rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right, SemidirectProduct.right_inl,
        one_mul, mul_one, hTr]
  have hc := congrArg (conjAct Q) hpair
  rw [map_mul, map_mul, hconjT, conjAct_inclusion_of_mem ⟨h', hh'O⟩ hh'Ω] at hc
  refine ⟨(MulAut.conj ⟨h', hh'Ω⟩)⁻¹, inv_mem ⟨_, rfl⟩, ?_⟩
  rw [inv_inv, mul_assoc]
  exact eq_inv_mul_of_mul_eq hc

end Conj

end RecipeFieldOmega

end CFSG.StandardType

end
