module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaLang

public section

namespace CFSG.StandardType

open CFSG.Assembly QuadraticMap CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.RankThree.PartOne.AUTSL

namespace RecipeFieldOmega

section Conj

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem polar_isIsoPair {g : coordinateSemilinearGroup d K} (hg : IsIsoPair Q g)
    (x y : Fin d → K) :
    polar Q (coordinateSemilinearMap g x) (coordinateSemilinearMap g y) =
      g.right (polar Q x y) := by
  rw [polar, polar, ← map_add, hg, hg, hg, map_sub, map_sub]

theorem IsIsoPair.mul {g g' : coordinateSemilinearGroup d K} (hg : IsIsoPair Q g)
    (hg' : IsIsoPair Q g') : IsIsoPair Q (g * g') := fun v => by
  rw [coordinateSemilinearMap_mul, hg, hg']
  rfl

theorem IsIsoPair.pow {g : coordinateSemilinearGroup d K} (hg : IsIsoPair Q g) (k : ℕ) :
    IsIsoPair Q (g ^ k) := by
  induction k with
  | zero => exact fun v => by rw [pow_zero, coordinateSemilinearMap_one]; rfl
  | succ k ih => rw [pow_succ]; exact ih.mul hg

theorem isIsoPair_inl {A : GL (Fin d) K} (hA : A ∈ matrixIsometries Q) :
    IsIsoPair Q (SemidirectProduct.inl A) := fun v => by
  rw [coordinateSemilinearMap_inl]
  exact (mem_matrixIsometries_iff Q A).1 hA v

theorem reflMat_mul_eq_of_isIsoPair {S : coordinateSemilinearGroup d K} (hS : IsIsoPair Q S)
    {w : Fin d → K} (hw : Q w ≠ 0) (hSw : coordinateSemilinearMap S w = w) :
    reflMat Q w hw * S.left = S.left * glFieldAut (Fin d) K S.right (reflMat Q w hw) := by
  set σ := S.right
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun u => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Units.val_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  set v : Fin d → K := fun i => σ.symm (u i)
  have hu : u = fun i => σ (v i) := funext fun i => (σ.apply_symm_apply _).symm
  have hSv : S.left.val.mulVec u = coordinateSemilinearMap S v := by
    rw [coordinateSemilinearMap_apply, hu]
  have hσr : (glFieldAut (Fin d) K σ (reflMat Q w hw)).val.mulVec u =
      fun i => σ (((reflMat Q w hw).val.mulVec v) i) := by
    funext i
    rw [hu]
    exact (RingHom.map_mulVec (σ : K →+* K) (reflMat Q w hw).val v i).symm
  rw [hσr, hSv, reflMat_mulVec, reflMat_mulVec, ← coordinateSemilinearMap_apply, map_sub,
    coordinateSemilinearMap_smul, hSw]
  congr 2
  have hpol := polar_isIsoPair hS w v
  rw [hSw] at hpol
  have hQw : σ (Q w) = Q w := by rw [← hS w, hSw]
  rw [map_div₀, hpol, hQw]

variable [Finite K] [CharP K 2]

theorem exists_derived_conj (hnd : Q.polarBilin.Nondegenerate)
    (hT3 : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {S : coordinateSemilinearGroup d K} (hS : IsIsoPair Q S) {w : Fin d → K} (hw : Q w ≠ 0)
    (hSw : coordinateSemilinearMap S w = w) {B h : GL (Fin d) K} (hh : h ∈ matrixIsometries Q)
    (heq : h * B = S.left * glFieldAut (Fin d) K S.right h) :
    ∃ h' ∈ matrixDerived Q, h' * B = S.left * glFieldAut (Fin d) K S.right h' := by
  rcases mem_or_mul_reflMat_mem hnd hT3 hh w hw with hΩ | hΩ
  · exact ⟨h, hΩ, heq⟩
  · have hr := reflMat_mem_isometries (Q := Q) w hw
    refine ⟨reflMat Q w hw * h, ?_, ?_⟩
    · have hmem := (conjAct Q (matrixIsometryInclusion Q ⟨reflMat Q w hw, hr⟩) ⟨_, hΩ⟩).2
      rw [conjAct_inclusion_val] at hmem
      have e : reflMat Q w hw * (h * reflMat Q w hw) * (reflMat Q w hw)⁻¹ =
          reflMat Q w hw * h := by group
      rw [← e]
      exact hmem
    · rw [mul_assoc, heq, ← mul_assoc, reflMat_mul_eq_of_isIsoPair hS hw hSw, mul_assoc, ← map_mul]

omit [Finite K] in
theorem eq_one_of_conjAct_eq_one (hnd : Q.polarBilin.Nondegenerate)
    (hT3 : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hAP : CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.ActionProperties Q
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.projectivePointAction Q))
    (hQne : ∃ v, Q v ≠ 0) {g : similarityPairs Q} (hg : IsIsoPair Q g.val)
    (h1 : conjAct Q g = 1) : g = 1 := by
  obtain ⟨a, ha⟩ := scalar_of_conjAct_eq_one hnd hT3 hAP h1
  have hr : g.val.right = 1 := AutOm.right_eq_one_of_conjAct_mem_inner hnd hT3 hAP (h1 ▸ one_mem _)
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin d) a ∈ matrixIsometries Q := by
    rw [mem_matrixIsometries_iff]
    intro v
    have := hg v
    rw [coordinateSemilinearMap_apply, hr, ha] at this
    exact this
  have ha1 := scalar_eq_one_of_mem_isometries hQne hmem
  apply Subtype.ext
  refine SemidirectProduct.ext ?_ hr
  rw [ha, ha1, map_one]
  rfl

theorem exists_conj_of_isIsoPair {n : ℕ} (hn : 1 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hnd : Q.polarBilin.Nondegenerate)
    (hT3 : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hAP : CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.ActionProperties Q
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.projectivePointAction Q))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : similarityPairs Q} (hS : IsIsoPair Q S.val)
    {w : Fin (2 * n) → K} (hw : Q w ≠ 0) (hSw : coordinateSemilinearMap S.val w = w)
    (γ : matrixDerived Q) (hout : MulAut.conj γ * conjAct Q S ∉ inner (matrixDerived Q))
    (hord : (MulAut.conj γ * conjAct Q S) ^ p = 1) (hfp : conjAct Q S ^ p = 1) :
    ∃ u' ∈ inner (matrixDerived Q), MulAut.conj γ * conjAct Q S = u' * conjAct Q S * u'⁻¹ := by
  have hQne : ∃ v, Q v ≠ 0 := ⟨w, hw⟩
  have hγO : γ.val ∈ matrixIsometries Q := matrixDerived_le_isometries _ γ.2
  have : Fact p.Prime := ⟨hp⟩
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
  have hσp : S.val.right ^ p = 1 := by rw [← right_pow, hSpv]; rfl
  have hσ1 : S.val.right ≠ 1 := by
    intro hσ1
    have hTl : T.val = SemidirectProduct.inl T.val.left := by
      refine SemidirectProduct.ext rfl ?_
      rw [hTr, SemidirectProduct.right_inl]
      exact hσ1
    have hBO : T.val.left ∈ matrixIsometries Q := by
      rw [mem_matrixIsometries_iff]
      intro v
      have := hT v
      rw [hTl, coordinateSemilinearMap_inl, SemidirectProduct.right_inl] at this
      exact this
    have hBΩ : T.val.left ∉ matrixDerived Q := by
      intro hΩ
      apply hout
      rw [← hconjT]
      have hT' : T = matrixIsometryInclusion Q ⟨_, hBO⟩ := Subtype.ext hTl
      rw [hT']
      exact conjAct_inclusion_mem_inner _ hΩ
    have hBp : T.val.left ^ p = 1 := by
      have h1 :
          (SemidirectProduct.inl T.val.left : coordinateSemilinearGroup (2 * n) K) ^ p = 1 := by
        rw [← hTl]
        exact hTpv
      have h2 := congrArg SemidirectProduct.left h1
      rwa [← map_pow, SemidirectProduct.left_inl] at h2
    apply hBΩ
    refine mem_of_pow_mem_of_coprime (matrixDerived Q) (a := 2) (N := p) ?_ hBp
      (Nat.coprime_two_left.2 (hp.odd_of_ne_two hp2))
    rw [_root_.sq]
    exact mul_self_mem_matrixDerived hnd hT3 hBO
  obtain ⟨h, hh, heq⟩ := exists_isometry_conj_of_isIsoPair hn hnd hp hp2 hS hT hTr
    (orderOf_eq_prime hσp hσ1) hSpv hTpv
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
