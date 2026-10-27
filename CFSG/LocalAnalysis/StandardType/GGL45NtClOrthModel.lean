module

public import CFSG.LocalAnalysis.StandardType.GGL45NtClOrth
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.HardMathSupport.C14Cl

open CFSG CFSG.Open CFSG.Assembly CFSG.StandardType QuadraticMap Matrix
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField

theorem omegaModel_conj_mem_aux {K : Type} [Field K] {n : ℕ} (Q : QuadraticForm K (Fin n → K))
    (H : GL (Fin n) K) {y : GL (Fin n) K}
    (hy : y ∈ matrixIsometries (Q.comp (Matrix.toLin' (H : Matrix (Fin n) (Fin n) K)))) :
    H * y * H⁻¹ ∈ matrixIsometries Q := by
  rw [mem_matrixIsometries_iff] at hy ⊢
  intro v
  have h := hy (matrixLinearEquiv (H⁻¹) v)
  simp only [QuadraticMap.comp_apply] at h
  have e1 : ∀ x, (Matrix.toLin' (H : Matrix (Fin n) (Fin n) K)) x = matrixLinearEquiv H x := fun x => by
    rw [Matrix.toLin'_apply, matrixLinearEquiv_apply]
  have e2 : matrixLinearEquiv H (matrixLinearEquiv H⁻¹ v) = v := by
    rw [← LinearEquiv.mul_apply, ← matrixLinearEquiv_mul, mul_inv_cancel]
    simp [matrixLinearEquiv]
  rw [e1, e1, e2] at h
  rw [← h, matrixLinearEquiv_mul, matrixLinearEquiv_mul]
  rfl

@[expose] noncomputable def omegaModelConj {K : Type} [Field K] {n : ℕ} (Q : QuadraticForm K (Fin n → K))
    (H : GL (Fin n) K) :
    ↥(matrixIsometries (Q.comp (Matrix.toLin' (H : Matrix (Fin n) (Fin n) K)))) →*
      MulAut ↥(matrixDerived Q) where
  toFun y := CFSG.RankThree.PartOne.AUTSL.conjAct Q (matrixIsometryInclusion Q
    ⟨H * (y : GL (Fin n) K) * H⁻¹, omegaModel_conj_mem_aux Q H y.2⟩)
  map_one' := by
    have h : (⟨H * ((1 : ↥(matrixIsometries (Q.comp (Matrix.toLin' (H : Matrix (Fin n) (Fin n) K))))) :
        GL (Fin n) K) * H⁻¹, omegaModel_conj_mem_aux Q H (1 : ↥(matrixIsometries (Q.comp
          (Matrix.toLin' (H : Matrix (Fin n) (Fin n) K))))).2⟩ : ↥(matrixIsometries Q)) = 1 :=
      Subtype.ext (by simp)
    rw [h, map_one, map_one]
  map_mul' x y := by
    have h : (⟨H * ((x * y : ↥(matrixIsometries (Q.comp (Matrix.toLin' (H : Matrix (Fin n) (Fin n) K))))) :
        GL (Fin n) K) * H⁻¹, omegaModel_conj_mem_aux Q H (x * y).2⟩ : ↥(matrixIsometries Q)) =
        ⟨H * (x : GL (Fin n) K) * H⁻¹, omegaModel_conj_mem_aux Q H x.2⟩ *
          ⟨H * (y : GL (Fin n) K) * H⁻¹, omegaModel_conj_mem_aux Q H y.2⟩ :=
      Subtype.ext (by
        change H * ((x : GL (Fin n) K) * (y : GL (Fin n) K)) * H⁻¹ =
          H * (x : GL (Fin n) K) * H⁻¹ * (H * (y : GL (Fin n) K) * H⁻¹)
        group)
    rw [h, map_mul, map_mul]

theorem omegaModelConj_apply_val {K : Type} [Field K] {n : ℕ} (Q : QuadraticForm K (Fin n → K))
    (H : GL (Fin n) K)
    (y : ↥(matrixIsometries (Q.comp (Matrix.toLin' (H : Matrix (Fin n) (Fin n) K)))))
    (γ : ↥(matrixDerived Q)) :
    ((omegaModelConj Q H y γ : ↥(matrixDerived Q)) : GL (Fin n) K) =
      (H * (y : GL (Fin n) K) * H⁻¹) * (γ : GL (Fin n) K) * (H * (y : GL (Fin n) K) * H⁻¹)⁻¹ :=
  CFSG.RankThree.PartOne.AUTSL.conjAct_inclusion_val
    ⟨H * (y : GL (Fin n) K) * H⁻¹, omegaModel_conj_mem_aux Q H y.2⟩ γ

private lemma cM1_exists_Q_ne_zero {K : Type} [Field K] {d : ℕ} (hd : 0 < d)
    (Q : QuadraticForm K (Fin d → K)) (hnd : (polarBilin Q).Nondegenerate) :
    ∃ v, Q v ≠ 0 := by
  by_contra h
  simp only [not_exists, not_ne_iff] at h
  let i : Fin d := ⟨0, hd⟩
  have hx : (Pi.single i (1 : K) : Fin d → K) ≠ 0 := by
    intro hz
    have h1 := congrFun hz i
    rw [Pi.single_eq_same, Pi.zero_apply] at h1
    exact one_ne_zero h1
  refine hx (hnd.1 (Pi.single i (1 : K)) fun z => ?_)
  rw [polarBilin_apply_apply]
  simp [polar, h]

theorem omegaModel_conj_injective {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    (Q : QuadraticForm K (Fin (2 * n) → K)) (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hAP : CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.ActionProperties Q
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.projectivePointAction Q))
    (H : GL (Fin (2 * n)) K) : Function.Injective (omegaModelConj Q H) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have hQne : ∃ v, Q v ≠ 0 := cM1_exists_Q_ne_zero (d := 2 * n) (by omega) Q hnd
  let B : ↥(matrixIsometries Q) :=
    ⟨H * (y : GL (Fin (2 * n)) K) * H⁻¹, omegaModel_conj_mem_aux Q H y.2⟩
  let S : similarityPairs Q := matrixIsometryInclusion Q B
  have hSv : S.val = SemidirectProduct.inl B.val := matrixIsometryInclusion_val Q B
  have hS : RecipeFieldOmega.IsIsoPair Q S.val := by
    rw [hSv]
    exact RecipeFieldOmega.isIsoPair_inl B.2
  have hconj : CFSG.RankThree.PartOne.AUTSL.conjAct Q S = omegaModelConj Q H y := rfl
  have hS1 : CFSG.RankThree.PartOne.AUTSL.conjAct Q S = 1 := by
    rw [hconj]
    exact hy
  have hS_eq_one : S = 1 :=
    RecipeFieldOmega.eq_one_of_conjAct_eq_one hnd hT hAP hQne hS hS1
  have hBval : B.val = 1 := by
    have h := congrArg Subtype.val hS_eq_one
    rw [hSv] at h
    exact SemidirectProduct.inl_injective (φ := glFieldAut (Fin (2 * n)) K) (by simpa using h)
  apply Subtype.ext
  change (y : GL (Fin (2 * n)) K) = 1
  have hHy : H * (y : GL (Fin (2 * n)) K) * H⁻¹ = 1 := hBval
  have hH : H * (y : GL (Fin (2 * n)) K) = H * 1 := by
    have := mul_inv_eq_one.mp hHy
    simpa using this
  exact mul_left_cancel hH

private theorem cM2_quad_sigma {K : Type} [Field K] {d : ℕ} (σ : K ≃+* K) (K₀ : Subfield K)
    (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x) (Q' : QuadraticForm K (Fin d → K))
    (hQ' : ∀ w : Fin d → K₀, Q' (RecipeFieldOmega.inclVec K₀ w) ∈ K₀) :
    ∀ w : Fin d → K, Q' (fun i => σ (w i)) = σ (Q' w) := by
  have hpol : ∀ u v : Fin d → K,
      QuadraticMap.polar (fun w => σ.symm (Q' (fun i => σ (w i)))) u v =
        σ.symm (QuadraticMap.polar Q' (fun i => σ (u i)) (fun i => σ (v i))) := by
    intro u v
    simp only [QuadraticMap.polar]
    have h1 : (fun i => σ ((u + v) i)) = (fun i => σ (u i)) + (fun i => σ (v i)) := by
      funext i; simp
    rw [h1, map_sub, map_sub]
  let Q'' : QuadraticForm K (Fin d → K) :=
    QuadraticMap.ofPolar (fun w => σ.symm (Q' (fun i => σ (w i))))
      (fun a w => by
        change σ.symm (Q' (fun i => σ ((a • w) i))) =
          (a * a) • σ.symm (Q' (fun i => σ (w i)))
        have h1 : (fun i => σ ((a • w) i)) = (σ a) • (fun i => σ (w i)) := by
          funext i; simp [Pi.smul_apply, smul_eq_mul]
        rw [h1, QuadraticMap.map_smul]
        simp only [smul_eq_mul, map_mul, RingEquiv.symm_apply_apply])
      (fun x x' y => by
        rw [hpol, hpol, hpol]
        have h1 : (fun i => σ ((x + x') i)) = (fun i => σ (x i)) + (fun i => σ (x' i)) := by
          funext i; simp
        rw [h1, QuadraticMap.polar_add_left, map_add])
      (fun a x y => by
        rw [hpol, hpol]
        have h1 : (fun i => σ ((a • x) i)) = (σ a) • (fun i => σ (x i)) := by
          funext i; simp [Pi.smul_apply, smul_eq_mul]
        rw [h1, QuadraticMap.polar_smul_left]
        simp only [smul_eq_mul, map_mul, RingEquiv.symm_apply_apply])
  have hQ'' : ∀ u : Fin d → K₀,
      Q'' (RecipeFieldOmega.inclVec K₀ u) = Q' (RecipeFieldOmega.inclVec K₀ u) := by
    intro u
    change σ.symm (Q' (fun i => σ ((u i : K)))) = Q' (RecipeFieldOmega.inclVec K₀ u)
    have hfix : (fun i => σ ((u i : K))) = RecipeFieldOmega.inclVec K₀ u := by
      funext i; exact (hK₀ (u i)).1 (u i).2
    rw [hfix]
    have hc1 : σ (Q' (RecipeFieldOmega.inclVec K₀ u)) = Q' (RecipeFieldOmega.inclVec K₀ u) :=
      (hK₀ _).1 (hQ' u)
    exact (σ.symm_apply_eq).2 hc1.symm
  have hQeq : Q'' = Q' := RecipeFieldOmega.eq_of_forall_inclVec K₀ hQ''
  intro w
  have h1 : Q'' w = Q' w := congr_fun hQeq w
  change σ.symm (Q' (fun i => σ (w i))) = Q' w at h1
  have h2 := congrArg σ h1
  simpa using h2

theorem omegaModel_frame {K : Type} [Field K] [Finite K] [CharP K 2] {n p : ℕ} (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (Q : QuadraticForm K (Fin (2 * n) → K))
    (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hAP : CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.ActionProperties Q
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.projectivePointAction Q))
    (S : similarityPairs Q) (hS : RecipeFieldOmega.IsIsoPair Q S.val)
    (hfp : orderOf (CFSG.RankThree.PartOne.AUTSL.conjAct Q S) = p)
    (hFinn : CFSG.RankThree.PartOne.AUTSL.conjAct Q S ∈ LargeEvenInnSet ↥(matrixDerived Q) →
      CFSG.RankThree.PartOne.AUTSL.conjAct Q S = 1) :
    ∃ (H : GL (Fin (2 * n)) K) (σ₀ : K ≃+* K), orderOf σ₀ = p ∧ S.val.right = σ₀ ∧
      S.val.left * glFieldAut (Fin (2 * n)) K σ₀ H = H ∧
      ∀ w : Fin (2 * n) → K,
        (Q.comp (Matrix.toLin' (H : Matrix (Fin (2 * n)) (Fin (2 * n)) K)))
            (fun i => σ₀ (w i)) =
          σ₀ ((Q.comp (Matrix.toLin' (H : Matrix (Fin (2 * n)) (Fin (2 * n)) K))) w) := by
  have hQne : ∃ v, Q v ≠ 0 := by
    by_contra h
    have hzero : ∀ v, Q v = 0 := by
      intro v
      by_contra hv
      exact h ⟨v, hv⟩
    have hpos : 0 < 2 * n := by omega
    have hnz : (Pi.single ⟨0, hpos⟩ (1 : K) : Fin (2 * n) → K) ≠ 0 := by
      intro hc
      have := congrFun hc ⟨0, hpos⟩
      simpa using this
    exact hnz (hnd.1 _ fun y => by
      simp [polarBilin_apply_apply, QuadraticMap.polar, hzero])
  have h1 : CFSG.RankThree.PartOne.AUTSL.conjAct Q (S ^ p) = 1 := by
    simpa [map_pow, hfp] using
      pow_orderOf_eq_one (CFSG.RankThree.PartOne.AUTSL.conjAct Q S)
  have hSp : S ^ p = 1 :=
    RecipeFieldOmega.eq_one_of_conjAct_eq_one hnd hT hAP hQne
      (by rw [SubmonoidClass.coe_pow]; exact hS.pow p) h1
  have hSpv : S.val ^ p = 1 := by rw [← SubmonoidClass.coe_pow, hSp]; rfl
  have hσpv : S.val.right ^ p = 1 := by rw [← RecipeFieldOmega.right_pow, hSpv]; rfl
  have hσ1 : S.val.right ≠ 1 := by
    intro hσ1
    have hSv : S.val = SemidirectProduct.inl S.val.left := by
      refine SemidirectProduct.ext rfl ?_
      rw [SemidirectProduct.right_inl]
      exact hσ1
    have hA : S.val.left ∈ matrixIsometries Q := by
      rw [mem_matrixIsometries_iff]
      intro v
      have hv := hS v
      rw [hSv, coordinateSemilinearMap_inl, SemidirectProduct.right_inl] at hv
      simpa using hv
    have hAp : S.val.left ^ p = 1 := by
      have h1 : (SemidirectProduct.inl S.val.left :
          coordinateSemilinearGroup (2 * n) K) ^ p = 1 := by
        rw [← hSv]; exact hSpv
      have h2 := congrArg SemidirectProduct.left h1
      rwa [← map_pow, SemidirectProduct.left_inl] at h2
    have hAΩ : S.val.left ∈ matrixDerived Q :=
      odd_mem_matrixDerived hp hp2 Q hnd hT hA ⟨1, by simpa using hAp⟩
    have hfinn : CFSG.RankThree.PartOne.AUTSL.conjAct Q S ∈ LargeEvenInnSet ↥(matrixDerived Q) := by
      have hSeq : S = matrixIsometryInclusion Q ⟨S.val.left, hA⟩ := by
        apply Subtype.ext
        rw [matrixIsometryInclusion_val]
        exact hSv
      rw [hSeq]
      exact CFSG.RankThree.PartOne.AUTSL.conjAct_inclusion_mem_inner ⟨S.val.left, hA⟩ hAΩ
    have hf1 : CFSG.RankThree.PartOne.AUTSL.conjAct Q S = 1 := hFinn hfinn
    have hp1 : p = 1 := by rw [← hfp, hf1, orderOf_one]
    exact hp.ne_one hp1
  haveI : Fact p.Prime := ⟨hp⟩
  have hσright : orderOf S.val.right = p := orderOf_eq_prime hσpv hσ1
  obtain ⟨H, hH⟩ := RecipeFieldOmega.exists_fixed_basis_pair (d := 2 * n) hp hσright rfl hSpv
  let K₀ : Subfield K := ((S.val.right : K ≃+* K) : K →+* K).eqLocusField (RingHom.id K)
  have hK₀ : ∀ x, x ∈ K₀ ↔ S.val.right x = x := fun x => Iff.rfl
  have hQ' : ∀ w : Fin (2 * n) → K₀,
      (Q.comp (Matrix.toLin' H.val)) (RecipeFieldOmega.inclVec K₀ w) ∈ K₀ :=
    fun w => RecipeFieldOmega.mem_fixed_of_isIsoPair hS rfl hK₀ hH w
  refine ⟨H, S.val.right, hσright, rfl, hH, ?_⟩
  intro w
  have hQσ := cM2_quad_sigma S.val.right K₀ hK₀ (Q.comp (Matrix.toLin' H.val)) hQ' w
  simpa using hQσ

theorem omegaModel_map_mem_isometries {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))
    (H : GL (Fin d) K) (σ₀ : K ≃+* K)
    (hQσ : ∀ w : Fin d → K,
      (Q.comp (Matrix.toLin' (H : Matrix (Fin d) (Fin d) K))) (fun i => σ₀ (w i)) =
        σ₀ ((Q.comp (Matrix.toLin' (H : Matrix (Fin d) (Fin d) K))) w))
    {y : GL (Fin d) K}
    (hy : y ∈ matrixIsometries (Q.comp (Matrix.toLin' (H : Matrix (Fin d) (Fin d) K)))) :
    glFieldAut (Fin d) K σ₀ y ∈
      matrixIsometries (Q.comp (Matrix.toLin' (H : Matrix (Fin d) (Fin d) K))) := by
  rw [mem_matrixIsometries_iff] at hy ⊢
  intro v
  have hQσ' : ∀ u : Fin d → K,
      (Q.comp (Matrix.toLin' (H : Matrix (Fin d) (Fin d) K))) (coordinateFieldMap d σ₀ u) =
        σ₀ ((Q.comp (Matrix.toLin' (H : Matrix (Fin d) (Fin d) K))) u) := fun u => hQσ u
  set w : Fin d → K := fun i => σ₀.symm (v i) with hw
  have hv : v = coordinateFieldMap d σ₀ w := by
    funext i
    simp [hw, coordinateFieldMap_apply]
  rw [hv, ← coordinateFieldMap_matrix (d := d) σ₀ y w]
  rw [hQσ' (matrixLinearEquiv y w), hy w, ← hQσ' w]

theorem omegaModel_sigma_conj {K : Type} [Field K] {n : ℕ} (Q : QuadraticForm K (Fin (2 * n) → K))
    (H : GL (Fin (2 * n)) K) (σ₀ : K ≃+* K) (S : similarityPairs Q) (hSr : S.val.right = σ₀)
    (hAH : S.val.left * glFieldAut (Fin (2 * n)) K σ₀ H = H)
    (y y' : ↥(matrixIsometries
      (Q.comp (Matrix.toLin' (H : Matrix (Fin (2 * n)) (Fin (2 * n)) K)))))
    (hyy' : ((y' : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      ((y : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K).map σ₀) :
    omegaModelConj Q H y' =
      CFSG.RankThree.PartOne.AUTSL.conjAct Q S * omegaModelConj Q H y *
        (CFSG.RankThree.PartOne.AUTSL.conjAct Q S)⁻¹ := by
  have hyy'_gl : (y' : GL (Fin (2 * n)) K) =
      glFieldAut (Fin (2 * n)) K σ₀ (y : GL (Fin (2 * n)) K) := by
    apply Units.ext
    rw [CFSG.StandardType.RecipeFieldOmega.glFieldAut_apply_val]
    exact hyy'
  have hfval : ∀ δ : ↥(matrixDerived Q),
      ((CFSG.RankThree.PartOne.AUTSL.conjAct Q S δ : ↥(matrixDerived Q)) :
          GL (Fin (2 * n)) K) =
        S.val.left * glFieldAut (Fin (2 * n)) K σ₀ (δ : GL (Fin (2 * n)) K) *
          S.val.left⁻¹ := by
    intro δ
    rw [CFSG.RankThree.PartOne.AUTSL.conjAct_apply, matrixDerivedConjugation_val, hSr]
  have hkey : omegaModelConj Q H y' * CFSG.RankThree.PartOne.AUTSL.conjAct Q S =
      CFSG.RankThree.PartOne.AUTSL.conjAct Q S * omegaModelConj Q H y := by
    refine MulEquiv.ext fun γ => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.mul_apply]
    rw [omegaModelConj_apply_val, hfval, hfval, omegaModelConj_apply_val, hyy'_gl]
    simp only [map_mul, map_inv]
    set X : GL (Fin (2 * n)) K := glFieldAut (Fin (2 * n)) K σ₀ H with hXdef
    have hAX : S.val.left * X = H := hAH
    set Y : GL (Fin (2 * n)) K := (y : GL (Fin (2 * n)) K) with hYdef
    set G : GL (Fin (2 * n)) K := (γ : GL (Fin (2 * n)) K) with hGdef
    rw [← hAX]
    group
  exact (eq_mul_inv_iff_mul_eq (a := omegaModelConj Q H y')
    (b := CFSG.RankThree.PartOne.AUTSL.conjAct Q S * omegaModelConj Q H y)
    (c := CFSG.RankThree.PartOne.AUTSL.conjAct Q S)).2 hkey

private lemma cM5_inner_mem_range {K : Type} [Field K] {n : ℕ}
    (Q : QuadraticForm K (Fin n → K)) (H : GL (Fin n) K) :
    ∀ w ∈ LargeEvenInnSet ↥(matrixDerived Q),
      ∃ y : ↥(matrixIsometries (Q.comp (Matrix.toLin' (H : Matrix (Fin n) (Fin n) K)))),
        omegaModelConj Q H y = w := by
  classical
  rintro w ⟨r, rfl⟩
  let x : GL (Fin n) K := H⁻¹ * (r : GL (Fin n) K) * H
  have hx : x ∈ matrixIsometries (Q.comp (Matrix.toLin' (H : Matrix (Fin n) (Fin n) K))) := by
    rw [mem_matrixIsometries_iff]
    intro v
    have e1 : ∀ u, (Matrix.toLin' (H : Matrix (Fin n) (Fin n) K)) u = matrixLinearEquiv H u :=
      fun u => by rw [Matrix.toLin'_apply, matrixLinearEquiv_apply]
    have hHx : H * x = (r : GL (Fin n) K) * H := by
      change H * (H⁻¹ * (r : GL (Fin n) K) * H) = (r : GL (Fin n) K) * H
      group
    have harg : matrixLinearEquiv H (matrixLinearEquiv x v) =
        matrixLinearEquiv (r : GL (Fin n) K) (matrixLinearEquiv H v) := by
      rw [← LinearEquiv.mul_apply, ← matrixLinearEquiv_mul, hHx, matrixLinearEquiv_mul,
        LinearEquiv.mul_apply]
    simp only [QuadraticMap.comp_apply]
    rw [e1, harg]
    exact (mem_matrixIsometries_iff Q (r : GL (Fin n) K)).mp
      (matrixDerived_le_isometries Q r.2) (matrixLinearEquiv H v)
  refine ⟨⟨x, hx⟩, ?_⟩
  have hxconj : H * x * H⁻¹ = (r : GL (Fin n) K) := by
    change H * (H⁻¹ * (r : GL (Fin n) K) * H) * H⁻¹ = (r : GL (Fin n) K)
    group
  change CFSG.RankThree.PartOne.AUTSL.conjAct Q (matrixIsometryInclusion Q
    ⟨H * x * H⁻¹, omegaModel_conj_mem_aux Q H hx⟩) = MulAut.conj r
  have hB : (⟨H * x * H⁻¹, omegaModel_conj_mem_aux Q H hx⟩ : ↥(matrixIsometries Q)) =
      ⟨(r : GL (Fin n) K), matrixDerived_le_isometries Q r.2⟩ :=
    Subtype.ext hxconj
  rw [hB, CFSG.RankThree.PartOne.AUTSL.conjAct_inclusion_of_mem _ r.2]

theorem omegaModel_E0_lift {K : Type} [Field K] [Finite K] [CharP K 2] {n p : ℕ} (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (Q : QuadraticForm K (Fin (2 * n) → K))
    (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hAP : CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.ActionProperties Q
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.projectivePointAction Q))
    (S : similarityPairs Q) (H : GL (Fin (2 * n)) K) (σ₀ : K ≃+* K) (hSr : S.val.right = σ₀)
    (hAH : S.val.left * glFieldAut (Fin (2 * n)) K σ₀ H = H)
    (hQσ : ∀ w : Fin (2 * n) → K,
      (Q.comp (Matrix.toLin' (H : Matrix (Fin (2 * n)) (Fin (2 * n)) K))) (fun i => σ₀ (w i)) =
        σ₀ ((Q.comp (Matrix.toLin' (H : Matrix (Fin (2 * n)) (Fin (2 * n)) K))) w))
    (Ebar : Subgroup (MulAut ↥(matrixDerived Q))) (hEab : IsElemAbelian p Ebar)
    (hEI : ∀ e ∈ Ebar, e ∈ LargeEvenInnSet ↥(matrixDerived Q))
    (hcomm : ∀ e ∈ Ebar, e * CFSG.RankThree.PartOne.AUTSL.conjAct Q S =
      CFSG.RankThree.PartOne.AUTSL.conjAct Q S * e) :
    ∃ E₀ : Subgroup ↥(matrixIsometries
        (Q.comp (Matrix.toLin' (H : Matrix (Fin (2 * n)) (Fin (2 * n)) K)))),
      IsElemAbelian p E₀ ∧
      (∀ e ∈ E₀, ((e : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K).map σ₀ =
        ((e : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K)) ∧
      ∀ e, e ∈ Ebar ↔ ∃ x ∈ E₀, omegaModelConj Q H x = e := by
  classical
  refine ⟨Ebar.comap (omegaModelConj Q H), ?_, ?_, ?_⟩
  ·
    exact hEab.comap (omegaModel_conj_injective hn Q hnd hT hAP H)
  ·
    intro e he
    let e' : ↥(matrixIsometries
        (Q.comp (Matrix.toLin' (H : Matrix (Fin (2 * n)) (Fin (2 * n)) K)))) :=
      ⟨(glFieldAut (Fin (2 * n)) K σ₀) (e : GL (Fin (2 * n)) K),
        omegaModel_map_mem_isometries Q H σ₀ hQσ e.2⟩
    have hyy' : ((e' : GL (Fin (2 * n)) K) :
          Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
        ((e : GL (Fin (2 * n)) K) :
          Matrix (Fin (2 * n)) (Fin (2 * n)) K).map σ₀ :=
      CFSG.StandardType.RecipeFieldOmega.glFieldAut_apply_val σ₀ (e : GL (Fin (2 * n)) K)
    have hconj := omegaModel_sigma_conj Q H σ₀ S hSr hAH e e' hyy'
    have hfix : CFSG.RankThree.PartOne.AUTSL.conjAct Q S * omegaModelConj Q H e *
        (CFSG.RankThree.PartOne.AUTSL.conjAct Q S)⁻¹ = omegaModelConj Q H e := by
      rw [← hcomm (omegaModelConj Q H e) he]
      group
    have heq : omegaModelConj Q H e' = omegaModelConj Q H e := by
      rw [hconj, hfix]
    have hE' : e' = e := omegaModel_conj_injective hn Q hnd hT hAP H heq
    calc ((e : GL (Fin (2 * n)) K) :
          Matrix (Fin (2 * n)) (Fin (2 * n)) K).map σ₀
        = ((e' : GL (Fin (2 * n)) K) :
            Matrix (Fin (2 * n)) (Fin (2 * n)) K) := hyy'.symm
      _ = ((e : GL (Fin (2 * n)) K) :
            Matrix (Fin (2 * n)) (Fin (2 * n)) K) :=
          congrArg (fun g : GL (Fin (2 * n)) K =>
            (g : Matrix (Fin (2 * n)) (Fin (2 * n)) K)) (congrArg Subtype.val hE')
  ·
    intro e
    constructor
    · intro he
      obtain ⟨x, hx⟩ := cM5_inner_mem_range Q H e (hEI e he)
      refine ⟨x, ?_, hx⟩
      show omegaModelConj Q H x ∈ Ebar
      rw [hx]
      exact he
    · rintro ⟨x, hx, rfl⟩
      exact hx

theorem omegaModel_conj_mem_inner_iff {K : Type} [Field K] [Finite K] [CharP K 2] {n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (Q : QuadraticForm K (Fin (2 * n) → K))
    (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (H : GL (Fin (2 * n)) K) :
    (∀ w ∈ LargeEvenInnSet ↥(matrixDerived Q), ∃ y : ↥(matrixIsometries
        (Q.comp (Matrix.toLin' (H : Matrix (Fin (2 * n)) (Fin (2 * n)) K)))), omegaModelConj Q H y = w) ∧
    ∀ y : ↥(matrixIsometries (Q.comp (Matrix.toLin' (H : Matrix (Fin (2 * n)) (Fin (2 * n)) K)))),
      (∃ k : ℕ, y ^ p ^ k = 1) → omegaModelConj Q H y ∈ LargeEvenInnSet ↥(matrixDerived Q) := by
  refine ⟨cM5_inner_mem_range Q H, ?_⟩
  intro y hy
  obtain ⟨k, hk⟩ := hy
  have hBmem : H * (y : GL (Fin (2 * n)) K) * H⁻¹ ∈ matrixIsometries Q :=
    omegaModel_conj_mem_aux Q H y.2
  have hy_pow : (y : GL (Fin (2 * n)) K) ^ (p ^ k) = 1 := by
    rw [← Subgroup.coe_pow, hk, OneMemClass.coe_one]
  have hBpow : (H * (y : GL (Fin (2 * n)) K) * H⁻¹) ^ (p ^ k) = 1 := by
    have h : H * (y : GL (Fin (2 * n)) K) * H⁻¹ =
        MulAut.conj H (y : GL (Fin (2 * n)) K) := by rw [MulAut.conj_apply]
    rw [h, ← map_pow, hy_pow, map_one]
  have hBder : H * (y : GL (Fin (2 * n)) K) * H⁻¹ ∈ matrixDerived Q :=
    odd_mem_matrixDerived hp hp2 Q hnd hT hBmem ⟨k, hBpow⟩
  refine ⟨⟨H * (y : GL (Fin (2 * n)) K) * H⁻¹, hBder⟩, ?_⟩
  exact (CFSG.RankThree.PartOne.AUTSL.conjAct_inclusion_of_mem
    ⟨H * (y : GL (Fin (2 * n)) K) * H⁻¹, omegaModel_conj_mem_aux Q H y.2⟩ hBder).symm

theorem omegaModel_sat_translate {K : Type} [Field K] [Finite K] [CharP K 2] {n p : ℕ} (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (Q : QuadraticForm K (Fin (2 * n) → K))
    (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hAP : CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.ActionProperties Q
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.projectivePointAction Q))
    (S : similarityPairs Q) (H : GL (Fin (2 * n)) K) (σ₀ : K ≃+* K) (hSr : S.val.right = σ₀)
    (hAH : S.val.left * glFieldAut (Fin (2 * n)) K σ₀ H = H)
    (Ebar : Subgroup (MulAut ↥(matrixDerived Q)))
    (E₀ : Subgroup ↥(matrixIsometries
        (Q.comp (Matrix.toLin' (H : Matrix (Fin (2 * n)) (Fin (2 * n)) K)))))
    (hE₀ : ∀ e, e ∈ Ebar ↔ ∃ x ∈ E₀, omegaModelConj Q H x = e)
    (hSatR : ∀ r : ↥(matrixDerived Q), r ^ p = 1 → (∀ e ∈ Ebar, e r = r) →
      CFSG.RankThree.PartOne.AUTSL.conjAct Q S r = r → MulAut.conj r ∈ Ebar) :
    ∀ y : ↥(matrixIsometries (Q.comp (Matrix.toLin' (H : Matrix (Fin (2 * n)) (Fin (2 * n)) K)))),
      (∀ e ∈ E₀, y * e = e * y) → y ^ p = 1 →
      ((y : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K).map σ₀ =
        ((y : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) →
      ((y : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) ∈
        spanE K (E₀.map (matrixIsometries
          (Q.comp (Matrix.toLin' (H : Matrix (Fin (2 * n)) (Fin (2 * n)) K)))).subtype) := by
  intro y hycomm hyp hyfix
  have hyGLpow : (y : GL (Fin (2 * n)) K) ^ p = 1 := by
    rw [← Subgroup.coe_pow, hyp, OneMemClass.coe_one]
  have hBmem : H * (y : GL (Fin (2 * n)) K) * H⁻¹ ∈ matrixIsometries Q :=
    omegaModel_conj_mem_aux Q H y.2
  have hBpow : (H * (y : GL (Fin (2 * n)) K) * H⁻¹) ^ p = 1 := by
    have h : H * (y : GL (Fin (2 * n)) K) * H⁻¹ =
        MulAut.conj H (y : GL (Fin (2 * n)) K) := by rw [MulAut.conj_apply]
    rw [h, ← map_pow, hyGLpow, map_one]
  have hBder : H * (y : GL (Fin (2 * n)) K) * H⁻¹ ∈ matrixDerived Q :=
    odd_mem_matrixDerived hp hp2 Q hnd hT hBmem ⟨1, by simpa using hBpow⟩
  let r : ↥(matrixDerived Q) := ⟨H * (y : GL (Fin (2 * n)) K) * H⁻¹, hBder⟩
  have hr : r ^ p = 1 := by
    apply Subtype.ext
    change (H * (y : GL (Fin (2 * n)) K) * H⁻¹) ^ p = 1
    exact hBpow
  have hκy : omegaModelConj Q H y = MulAut.conj r := by
    show CFSG.RankThree.PartOne.AUTSL.conjAct Q (matrixIsometryInclusion Q
      ⟨H * (y : GL (Fin (2 * n)) K) * H⁻¹,
        omegaModel_conj_mem_aux Q H y.2⟩) = MulAut.conj r
    exact CFSG.RankThree.PartOne.AUTSL.conjAct_inclusion_of_mem _ hBder
  have hgly : glFieldAut (Fin (2 * n)) K σ₀ (y : GL (Fin (2 * n)) K) =
      (y : GL (Fin (2 * n)) K) := by
    apply GeneralLinearGroup.ext
    intro i j
    change (glFieldEquiv (Fin (2 * n)) σ₀ (y : GL (Fin (2 * n)) K) :
      Matrix (Fin (2 * n)) (Fin (2 * n)) K) i j =
      ((y : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) i j
    rw [glFieldEquiv_entry]
    exact congrFun (congrFun hyfix i) j
  have hfixE : ∀ e ∈ Ebar, e r = r := by
    intro e he
    obtain ⟨x, hxE, hxeq⟩ := (hE₀ e).mp he
    rw [← hxeq]
    apply Subtype.ext
    rw [omegaModelConj_apply_val]
    have hxcomm : (x : GL (Fin (2 * n)) K) * (y : GL (Fin (2 * n)) K) =
        (y : GL (Fin (2 * n)) K) * (x : GL (Fin (2 * n)) K) := by
      have h := congrArg (fun w : ↥(matrixIsometries
          (Q.comp (Matrix.toLin' (H : Matrix (Fin (2 * n)) (Fin (2 * n)) K)))) =>
        (w : GL (Fin (2 * n)) K)) (hycomm x hxE).symm
      rwa [Subgroup.coe_mul, Subgroup.coe_mul] at h
    have hxy : (x : GL (Fin (2 * n)) K) * (y : GL (Fin (2 * n)) K) *
        (x : GL (Fin (2 * n)) K)⁻¹ = (y : GL (Fin (2 * n)) K) := by
      rw [hxcomm]; group
    change MulAut.conj H (x : GL (Fin (2 * n)) K) * MulAut.conj H (y : GL (Fin (2 * n)) K) *
      (MulAut.conj H (x : GL (Fin (2 * n)) K))⁻¹ = H * (y : GL (Fin (2 * n)) K) * H⁻¹
    rw [← map_mul, ← map_inv, ← map_mul, hxy, MulAut.conj_apply]
  have hglB : glFieldAut (Fin (2 * n)) K σ₀ (H * (y : GL (Fin (2 * n)) K) * H⁻¹) =
      glFieldAut (Fin (2 * n)) K σ₀ H * (y : GL (Fin (2 * n)) K) *
        (glFieldAut (Fin (2 * n)) K σ₀ H)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hgly]
  have hfixf : CFSG.RankThree.PartOne.AUTSL.conjAct Q S r = r := by
    apply Subtype.ext
    rw [CFSG.RankThree.PartOne.AUTSL.conjAct_apply, matrixDerivedConjugation_val, hSr, hglB]
    calc S.val.left * (glFieldAut (Fin (2 * n)) K σ₀ H * (y : GL (Fin (2 * n)) K) *
            (glFieldAut (Fin (2 * n)) K σ₀ H)⁻¹) * S.val.left⁻¹
        = (S.val.left * glFieldAut (Fin (2 * n)) K σ₀ H) * (y : GL (Fin (2 * n)) K) *
            (S.val.left * glFieldAut (Fin (2 * n)) K σ₀ H)⁻¹ := by group
      _ = H * (y : GL (Fin (2 * n)) K) * H⁻¹ := by rw [hAH]
  have hrSat : MulAut.conj r ∈ Ebar := hSatR r hr hfixE hfixf
  obtain ⟨x, hxE, hxeq⟩ := (hE₀ (MulAut.conj r)).mp hrSat
  have hxy_eq : x = y := (omegaModel_conj_injective hn Q hnd hT hAP H) (by rw [hxeq, hκy])
  have hyE : y ∈ E₀ := hxy_eq ▸ hxE
  exact Submodule.subset_span
    ⟨⟨(y : GL (Fin (2 * n)) K), Subgroup.mem_map.mpr ⟨y, hyE, rfl⟩⟩, rfl⟩

private theorem cM8_vec_eq_of_dotProduct_eq {K : Type} [Field K] {d : ℕ}
    {u v : Fin d → K} (h : ∀ x, x ⬝ᵥ u = x ⬝ᵥ v) : u = v := by
  funext i
  have := h (Pi.single i (1 : K))
  simpa [single_one_dotProduct] using this

private theorem cM8_mat_eq_of_mulVec_eq {K : Type} [Field K] {d : ℕ}
    {M N : Matrix (Fin d) (Fin d) K} (h : ∀ v, M *ᵥ v = N *ᵥ v) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j (1 : K))) i
  simpa [Matrix.mulVec_single_one] using this

private theorem cM8_mat_eq_of_dotProduct_eq {K : Type} [Field K] {d : ℕ}
    {M N : Matrix (Fin d) (Fin d) K}
    (h : ∀ x y, x ⬝ᵥ (M *ᵥ y) = x ⬝ᵥ (N *ᵥ y)) : M = N := by
  apply cM8_mat_eq_of_mulVec_eq
  intro y
  apply cM8_vec_eq_of_dotProduct_eq
  intro x
  exact h x y

private theorem cM8_isElemAbelian_map {G G' : Type*} [Group G] [Group G'] {p : ℕ}
    {E : Subgroup G} (hE : IsElemAbelian p E) (f : G →* G') (hf : Function.Injective f) :
    IsElemAbelian p (E.map f) := by
  haveI := hE.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx, hax⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨z, hz, hbz⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    change (a : G') * b = b * a
    rw [← hax, ← hbz, ← map_mul, ← map_mul]
    exact congrArg (fun w : E => f w) (mul_comm' (⟨x, hx⟩ : E) ⟨z, hz⟩)
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_pow, hE.2 x hx, map_one]

private theorem cM8_sigma_single {K : Type} [Field K] {d : ℕ} (σ : K ≃+* K) (i : Fin d) :
    ∀ j, σ ((Pi.single i (1 : K) : Fin d → K) j) =
      (Pi.single i (1 : K) : Fin d → K) j := by
  intro j
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_apply, h]

private theorem cM8_polar_sigma_fixed {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (σ : K ≃+* K)
    (hQσ : ∀ w : Fin d → K, Q (fun i => σ (w i)) = σ (Q w))
    {x y : Fin d → K} (hx : ∀ i, σ (x i) = x i) (hy : ∀ i, σ (y i) = y i) :
    σ (polar Q x y) = polar Q x y := by
  have hσx : (fun i => σ (x i)) = x := funext hx
  have hσy : (fun i => σ (y i)) = y := funext hy
  have hxy : (fun i => σ ((x + y) i)) = x + y := by
    funext i; rw [Pi.add_apply, map_add, hx i, hy i]
  calc σ (polar Q x y) = σ (Q (x + y)) - σ (Q x) - σ (Q y) := by
        rw [polar, map_sub, map_sub]
    _ = Q (fun i => σ ((x + y) i)) - Q (fun i => σ (x i)) - Q (fun i => σ (y i)) := by
        rw [← hQσ (x + y), ← hQσ x, ← hQσ y]
    _ = Q (x + y) - Q x - Q y := by rw [hxy, hσx, hσy]
    _ = polar Q x y := by rw [polar]

private theorem cM8_toMatrix'_transpose {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) :
    (LinearMap.BilinForm.toMatrix' (polarBilin Q))ᵀ =
      LinearMap.BilinForm.toMatrix' (polarBilin Q) := by
  ext i j
  simp only [Matrix.transpose_apply, LinearMap.BilinForm.toMatrix'_apply,
    QuadraticMap.polarBilin_apply_apply]
  exact (QuadraticMap.polar_comm Q (Pi.single i (1 : K)) (Pi.single j (1 : K))).symm

private theorem cM8_toMatrix'_map_sigma {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (σ : K ≃+* K)
    (hQσ : ∀ w : Fin d → K, Q (fun i => σ (w i)) = σ (Q w)) :
    (LinearMap.BilinForm.toMatrix' (polarBilin Q)).map σ =
      LinearMap.BilinForm.toMatrix' (polarBilin Q) := by
  ext i j
  simp only [Matrix.map_apply, LinearMap.BilinForm.toMatrix'_apply,
    QuadraticMap.polarBilin_apply_apply]
  exact cM8_polar_sigma_fixed Q σ hQσ (cM8_sigma_single σ i) (cM8_sigma_single σ j)

private theorem cM8_formAdj_mul_eq_one {K : Type} [Field K] {d : ℕ}
    (G : Matrix (Fin d) (Fin d) K) (hG : IsUnit G.det)
    (Q : QuadraticForm K (Fin d → K))
    (hQG : ∀ x y : Fin d → K, polar Q x y = x ⬝ᵥ (G *ᵥ y))
    {g : GL (Fin d) K} (hg : g ∈ matrixIsometries Q) :
    formAdj (RingEquiv.refl K) G (g : Matrix (Fin d) (Fin d) K) *
      (g : Matrix (Fin d) (Fin d) K) = 1 := by
  have hpol : ∀ x y, polar Q ((g : Matrix (Fin d) (Fin d) K) *ᵥ x)
      ((g : Matrix (Fin d) (Fin d) K) *ᵥ y) = polar Q x y :=
    fun x y => CFSG.RankThree.PartOne.AUTSL.polar_mulVec_of_mem hg x y
  have hmat : (g : Matrix (Fin d) (Fin d) K)ᵀ * G * (g : Matrix (Fin d) (Fin d) K) = G := by
    apply cM8_mat_eq_of_dotProduct_eq
    intro x y
    have hkey : x ⬝ᵥ (((g : Matrix (Fin d) (Fin d) K)ᵀ * G *
        (g : Matrix (Fin d) (Fin d) K)) *ᵥ y) =
        ((g : Matrix (Fin d) (Fin d) K) *ᵥ x) ⬝ᵥ
          (G *ᵥ ((g : Matrix (Fin d) (Fin d) K) *ᵥ y)) := by
      conv_lhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose]
    rw [hkey, ← hQG, hpol, hQG]
  have hmap : (g : Matrix (Fin d) (Fin d) K).map (RingEquiv.refl K) =
      (g : Matrix (Fin d) (Fin d) K) := rfl
  rw [formAdj, hmap]
  calc G⁻¹ * (g : Matrix (Fin d) (Fin d) K)ᵀ * G * (g : Matrix (Fin d) (Fin d) K)
      = G⁻¹ * ((g : Matrix (Fin d) (Fin d) K)ᵀ * G * (g : Matrix (Fin d) (Fin d) K)) := by
        simp only [Matrix.mul_assoc]
    _ = G⁻¹ * G := by rw [hmat]
    _ = 1 := Matrix.nonsing_inv_mul _ hG

theorem ntCore_omega_single {K : Type} [Field K] [Finite K] [CharP K 2] {n p : ℕ} (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (Q : QuadraticForm K (Fin (2 * n) → K))
    (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hAP : CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.ActionProperties Q
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.projectivePointAction Q))
    (S : similarityPairs Q) (hS : RecipeFieldOmega.IsIsoPair Q S.val)
    (hFinn : CFSG.RankThree.PartOne.AUTSL.conjAct Q S ∈ LargeEvenInnSet ↥(matrixDerived Q) →
      CFSG.RankThree.PartOne.AUTSL.conjAct Q S = 1) :
    GGL45NtCore p ↥(matrixDerived Q) (LargeEvenInnSet ↥(matrixDerived Q))
      {CFSG.RankThree.PartOne.AUTSL.conjAct Q S} := by
  haveI : Fintype K := Fintype.ofFinite K
  refine ntCore_of_conj p (LargeEvenInnSet ↥(matrixDerived Q))
    {CFSG.RankThree.PartOne.AUTSL.conjAct Q S} ?_ ?_ ?_
  · rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
    exact ⟨a * b⁻¹, by rw [map_mul, map_inv]⟩
  · exact ⟨1, map_one _⟩
  · intro hsimp hnab Ebar f₁ hEab hcard hEI hf₁F hf₁o hcomm hSat
    rw [Set.mem_singleton_iff] at hf₁F
    subst hf₁F
    obtain ⟨H, σ₀, hσ₀, hSr, hAH, hQσ⟩ :=
      omegaModel_frame hn hp hp2 Q hnd hT hAP S hS hf₁o hFinn
    obtain ⟨E₀, hE₀ab, hE₀fix, hE₀Ebar⟩ :=
      omegaModel_E0_lift hn hp hp2 Q hnd hT hAP S H σ₀ hSr hAH hQσ Ebar hEab hEI hcomm
    let Q' : QuadraticForm K (Fin (2 * n) → K) :=
      Q.comp (Matrix.toLin' (H : Matrix (Fin (2 * n)) (Fin (2 * n)) K))
    have hndQ' : (polarBilin Q').Nondegenerate := RecipeFieldOmega.nondegenerate_comp_GL hnd H
    let G : Matrix (Fin (2 * n)) (Fin (2 * n)) K :=
      LinearMap.BilinForm.toMatrix' (polarBilin Q')
    have hQG : ∀ x y : Fin (2 * n) → K, polar Q' x y = x ⬝ᵥ (G *ᵥ y) := by
      intro x y
      change polar Q' x y = x ⬝ᵥ (LinearMap.BilinForm.toMatrix' (polarBilin Q') *ᵥ y)
      rw [← Matrix.toBilin'_apply', Matrix.toBilin'_toMatrix',
        QuadraticMap.polarBilin_apply_apply]
    have hGdet : IsUnit G.det := by
      rw [isUnit_iff_ne_zero]
      have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
        (Pi.basisFun K (Fin (2 * n)))).mp hndQ'
      rwa [LinearMap.BilinForm.toMatrix_basisFun] at h
    have hGs : (G.map (RingEquiv.refl K))ᵀ = G := by
      change ((LinearMap.BilinForm.toMatrix' (polarBilin Q')).map (RingEquiv.refl K))ᵀ =
        LinearMap.BilinForm.toMatrix' (polarBilin Q')
      rw [show (LinearMap.BilinForm.toMatrix' (polarBilin Q')).map (RingEquiv.refl K) =
          LinearMap.BilinForm.toMatrix' (polarBilin Q') from by ext i j; rfl]
      exact cM8_toMatrix'_transpose Q'
    have hGσ : G.map σ₀ = G := by
      change (LinearMap.BilinForm.toMatrix' (polarBilin Q')).map σ₀ =
        LinearMap.BilinForm.toMatrix' (polarBilin Q')
      exact cM8_toMatrix'_map_sigma Q' σ₀ hQσ
    have hE_C : IsElemAbelian p (E₀.map (matrixIsometries Q').subtype) :=
      cM8_isElemAbelian_map hE₀ab (matrixIsometries Q').subtype Subtype.val_injective
    have hEU_C : ∀ e ∈ E₀.map (matrixIsometries Q').subtype,
        formAdj (RingEquiv.refl K) G e * e = 1 := by
      rintro e ⟨x, hx, rfl⟩
      exact cM8_formAdj_mul_eq_one G hGdet Q' hQG x.2
    have hEfix_C : ∀ e ∈ E₀.map (matrixIsometries Q').subtype,
        ((e : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K).map σ₀ =
          ((e : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) := by
      rintro e ⟨x, hx, rfl⟩
      exact hE₀fix x hx
    let C : ClSetting K (Fin (2 * n)) :=
      { p := p
        hp := hp
        hp2 := hp2
        τ := RingEquiv.refl K
        hτ := fun c => rfl
        G := G
        hG := hGdet
        hGs := hGs
        σ₀ := σ₀
        hσ₀ := hσ₀
        hGσ := hGσ
        E₀ := E₀.map (matrixIsometries Q').subtype
        hE := hE_C
        hEU := hEU_C
        hEfix := hEfix_C }
    have hEQ : ∀ e ∈ C.E₀, e ∈ matrixIsometries Q' := by
      rintro e ⟨x, hx, rfl⟩
      exact x.2
    have hH : C.GoodGroup (matrixIsometries Q') :=
      orth_goodGroup_gen C rfl Q' hQG hQσ hEQ
    have hcardE0 : Nat.card E₀ = Nat.card Ebar := by
      let κ := omegaModelConj Q H
      have hκinj : Function.Injective κ := omegaModel_conj_injective hn Q hnd hT hAP H
      let ψ : E₀ → Ebar := fun x => ⟨κ x, (hE₀Ebar _).mpr ⟨x, x.2, rfl⟩⟩
      have hψ : Function.Bijective ψ := by
        constructor
        · intro x y hxy
          exact Subtype.ext (hκinj (Subtype.ext_iff.mp hxy))
        · rintro ⟨e, he⟩
          obtain ⟨x, hx, hxe⟩ := (hE₀Ebar e).mp he
          exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
      exact Nat.card_congr (Equiv.ofBijective ψ hψ)
    have hcardC : C.p ^ 2 ≤ Nat.card C.E₀ := by
      change p ^ 2 ≤ Nat.card (E₀.map (matrixIsometries Q').subtype)
      rw [Subgroup.card_map_of_injective (f := (matrixIsometries Q').subtype)
        Subtype.val_injective, hcardE0]
      exact hcard
    have hSatC : C.Sat (matrixIsometries Q') := by
      intro y hyH hyCent hyp hyσ
      have hyfix : ((y : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K).map σ₀ =
          ((y : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) := by
        have hh := congrArg (fun z : GL (Fin (2 * n)) K =>
          (z : Matrix (Fin (2 * n)) (Fin (2 * n)) K)) hyσ
        simpa [ClSetting.σGL, ClSetting.σ, RingEquiv.mapMatrix_apply] using hh
      have hyp' : (⟨y, hyH⟩ : ↥(matrixIsometries Q')) ^ p = 1 := by
        apply Subtype.ext
        simpa using hyp
      have hcommE : ∀ e ∈ E₀,
          (⟨y, hyH⟩ : ↥(matrixIsometries Q')) * e =
            e * (⟨y, hyH⟩ : ↥(matrixIsometries Q')) := by
        intro e he
        apply Subtype.ext
        exact hyCent.2 (e : GL (Fin (2 * n)) K) (Subgroup.mem_map.mpr ⟨e, he, rfl⟩)
      exact omegaModel_sat_translate hn hp hp2 Q hnd hT hAP S H σ₀ hSr hAH Ebar E₀ hE₀Ebar hSat
        ⟨y, hyH⟩ hcommE hyp' hyfix
    have hsub : C.E₀.subgroupOf (matrixIsometries Q') = E₀ := by
      apply Subgroup.map_injective (f := (matrixIsometries Q').subtype) Subtype.val_injective
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_of_le_left (Subgroup.map_subtype_le E₀)
    have hcl : ClCoreConcl p E₀ (C.sigmaOn hH) := by
      have hh := C.clCoreConcl hH hSatC hEQ hcardC
      rwa [hsub] at hh
    have hα : ∀ h : ↥(matrixIsometries Q'),
        omegaModelConj Q H (C.sigmaOn hH h) =
          CFSG.RankThree.PartOne.AUTSL.conjAct Q S * omegaModelConj Q H h *
            (CFSG.RankThree.PartOne.AUTSL.conjAct Q S)⁻¹ := by
      intro h
      have hyy' : (((C.sigmaOn hH h : ↥(matrixIsometries Q')) : GL (Fin (2 * n)) K) :
            Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
          (((h : ↥(matrixIsometries Q')) : GL (Fin (2 * n)) K) :
            Matrix (Fin (2 * n)) (Fin (2 * n)) K).map σ₀ :=
        rfl
      exact omegaModel_sigma_conj Q H σ₀ S hSr hAH h (C.sigmaOn hH h) hyy'
    have hqinj : ∀ x ∈ E₀, ∀ y ∈ E₀, omegaModelConj Q H x = omegaModelConj Q H y → x = y :=
      fun x _ y _ hxy => omegaModel_conj_injective hn Q hnd hT hAP H hxy
    have hcomm' : ∀ h : ↥(matrixIsometries Q'),
        (∀ e ∈ E₀, omegaModelConj Q H h * omegaModelConj Q H e =
          omegaModelConj Q H e * omegaModelConj Q H h) → ∀ e ∈ E₀, h * e = e * h := by
      intro h hh e he
      apply omegaModel_conj_injective hn Q hnd hT hAP H
      rw [map_mul, map_mul]
      exact hh e he
    exact coreConcl_transfer hp (LargeEvenInnSet ↥(matrixDerived Q)) Ebar
      (CFSG.RankThree.PartOne.AUTSL.conjAct Q S) (omegaModelConj Q H) (C.sigmaOn hH) hα E₀
      hqinj hE₀Ebar (omegaModel_conj_mem_inner_iff hp hp2 Q hnd hT H).1
      (omegaModel_conj_mem_inner_iff hp hp2 Q hnd hT H).2 hcomm' hcl

theorem ntCore_omega_model {K : Type} [Field K] [Finite K] [CharP K 2] {n p : ℕ} (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (Q : QuadraticForm K (Fin (2 * n) → K))
    (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hAP : CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.ActionProperties Q
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.projectivePointAction Q))
    (F : Set (MulAut ↥(matrixDerived Q)))
    (hF : ∀ f ∈ F, ∃ S : similarityPairs Q, RecipeFieldOmega.IsIsoPair Q S.val ∧
      CFSG.RankThree.PartOne.AUTSL.conjAct Q S = f)
    (hFinn : ∀ f ∈ F, f ∈ LargeEvenInnSet ↥(matrixDerived Q) → f = 1) :
    GGL45NtCore p ↥(matrixDerived Q) (LargeEvenInnSet ↥(matrixDerived Q)) F := by
  intro hsimp hnab Ebar f' hEab hcard hEI hf'p hconj hcomm hSat
  obtain ⟨f, hfF, u, huI, hford, hf'eq⟩ := hconj
  obtain ⟨S, hS, rfl⟩ := hF f hfF
  exact ntCore_omega_single hn hp hp2 Q hnd hT hAP S hS (hFinn _ hfF) hsimp hnab Ebar f' hEab hcard
    hEI hf'p ⟨CFSG.RankThree.PartOne.AUTSL.conjAct Q S, rfl, u, huI, hford, hf'eq⟩ hcomm hSat

end CFSG.HardMathSupport.C14Cl
