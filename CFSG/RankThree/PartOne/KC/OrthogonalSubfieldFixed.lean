module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBasic
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
public import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge

public section

open Matrix QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer (matrixLinearEquiv_scalar)

namespace CFSG.RankThree.PartOne.KCOrthogonalSubfield

section Fixed

open CFSG.ComponentClassification.CatalogueBHigherLinearField

variable {K : Type} [Field K] (k : Subfield K) {d : ℕ}

@[expose] noncomputable def subfieldIsometries (Q₀ : QuadraticForm k (Fin d → k))
    (Q : QuadraticForm K (Fin d → K)) : Subgroup (matrixDerived Q) :=
  ((matrixIsometries Q₀).map (glIncl k)).subgroupOf (matrixDerived Q)

@[expose] noncomputable def subfieldFixedGroup (Q₀ : QuadraticForm k (Fin d → k))
    (Q : QuadraticForm K (Fin d → K)) : Subgroup (matrixProjectiveDerived Q) :=
  (subfieldIsometries k Q₀ Q).map (matrixProjectiveProjection Q)

@[expose] noncomputable def subfieldDerivedImage {Q₀ : QuadraticForm k (Fin d → k)}
    {Q : QuadraticForm K (Fin d → K)} (hext : IsExtension k Q₀ Q) :
    Subgroup (matrixProjectiveDerived Q) :=
  (incl k hext).range

variable (Q : QuadraticForm K (Fin d → K)) (σ : K ≃+* K)
  (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))

@[expose] noncomputable def fieldPair : similarityPairs Q :=
  ⟨⟨1, σ⟩, 1, fun v => by
    have h1 : coordinateSemilinearMap (⟨1, σ⟩ : coordinateSemilinearGroup d K) v =
        coordinateFieldMap d σ v := by
      funext i
      simp [coordinateSemilinearMap_apply, coordinateFieldMap_apply]
    rw [h1, hQσ]
    simp⟩

@[expose] noncomputable def fieldAutT : MulAut (matrixProjectiveDerived Q) :=
  matrixProjectiveConjugationHom Q (fieldPair Q σ hQσ)

theorem fieldPair_left : (fieldPair Q σ hQσ).val.left = 1 := rfl

theorem fieldPair_right : (fieldPair Q σ hQσ).val.right = σ := rfl

theorem fieldAutT_mk (y : matrixDerived Q) :
    fieldAutT Q σ hQσ (matrixProjectiveProjection Q y) =
      matrixProjectiveProjection Q (matrixDerivedConjugation Q (fieldPair Q σ hQσ) y) :=
  matrixProjectiveConjugation_mk Q _ y

theorem matrixDerivedConjugation_fieldPair_val (y : matrixDerived Q) :
    ((matrixDerivedConjugation Q (fieldPair Q σ hQσ) y : matrixDerived Q) : GL (Fin d) K) =
      glFieldAut (Fin d) K σ y.val := by
  rw [matrixDerivedConjugation_val, fieldPair_left, fieldPair_right]
  simp

theorem glFieldAut_glIncl {σ : K ≃+* K} (hσk : ∀ x, x ∈ k ↔ σ x = x) (x : GL (Fin d) k) :
    glFieldAut (Fin d) K σ (glIncl k x) = glIncl k x := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change σ ((glIncl k x).val i j) = (glIncl k x).val i j
  exact (hσk _).mp (x.val i j).2

theorem fieldAutT_fixes_J {Q₀ : QuadraticForm k (Fin d → k)} (hext : IsExtension k Q₀ Q)
    (hσk : ∀ x, x ∈ k ↔ σ x = x) {t : matrixProjectiveDerived Q}
    (ht : t ∈ subfieldDerivedImage k hext) : fieldAutT Q σ hQσ t = t := by
  obtain ⟨z, rfl⟩ := ht
  obtain ⟨y, rfl⟩ := matrixProjectiveProjection_surjective Q₀ z
  rw [incl_mk, fieldAutT_mk]
  congr 1
  apply Subtype.ext
  rw [matrixDerivedConjugation_fieldPair_val, inclHom_val, glFieldAut_glIncl k hσk]

theorem exists_glIncl_of_fixed {σ : K ≃+* K} (hσk : ∀ x, x ∈ k ↔ σ x = x) {Y : GL (Fin d) K}
    (hY : glFieldAut (Fin d) K σ Y = Y) : ∃ x : GL (Fin d) k, glIncl k x = Y := by
  have hent : ∀ (Z : GL (Fin d) K), glFieldAut (Fin d) K σ Z = Z → ∀ i j, Z.val i j ∈ k :=
    fun Z hZ i j => (hσk _).mpr (by
      have := congrArg (fun B : GL (Fin d) K => B.val i j) hZ
      exact this)
  have hY' : glFieldAut (Fin d) K σ Y⁻¹ = Y⁻¹ := by rw [map_inv, hY]
  let x₀ : Matrix (Fin d) (Fin d) k := fun i j => ⟨Y.val i j, hent Y hY i j⟩
  let x₁ : Matrix (Fin d) (Fin d) k := fun i j => ⟨(Y⁻¹).val i j, hent Y⁻¹ hY' i j⟩
  have hx₀ : x₀.map k.subtype = Y.val := rfl
  have hx₁ : x₁.map k.subtype = (Y⁻¹).val := rfl
  have h01 : x₀ * x₁ = 1 := by
    apply Matrix.map_injective (f := k.subtype) k.subtype_injective
    show (x₀ * x₁).map k.subtype = (1 : Matrix (Fin d) (Fin d) k).map k.subtype
    rw [Matrix.map_mul, hx₀, hx₁, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Y.mul_inv
  have h10 : x₁ * x₀ = 1 := by
    apply Matrix.map_injective (f := k.subtype) k.subtype_injective
    show (x₁ * x₀).map k.subtype = (1 : Matrix (Fin d) (Fin d) k).map k.subtype
    rw [Matrix.map_mul, hx₀, hx₁, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Y.inv_mul
  exact ⟨⟨x₀, x₁, h01, h10⟩, Units.ext rfl⟩

end Fixed


section FixedGroup

open CFSG.ComponentClassification.CatalogueBHigherLinearField

theorem apply_eq_of_sq_apply_eq {G : Type*} [Group G] (S : MulAut G) {p : ℕ} (hp : Odd p)
    (hSp : S ^ p = 1) {Y : G} (h2 : S (S Y) = Y) : S Y = Y := by
  obtain ⟨m, rfl⟩ := hp
  have h22 : (S ^ 2) Y = Y := by
    rw [pow_two, MulAut.mul_apply]
    exact h2
  have h : ∀ j : ℕ, ((S ^ 2) ^ j) Y = Y := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, MulAut.mul_apply, h22, ih]
  have h3 : S ^ (2 * (m + 1)) = S := by
    have h4 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    rw [h4, pow_succ, hSp, one_mul]
  have := h (m + 1)
  rwa [← pow_mul, h3] at this

variable {K : Type} [Field K] (k : Subfield K) {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

theorem mem_isometries_of_glIncl (hext : IsExtension k Q₀ Q) {x : GL (Fin d) k}
    (hx : glIncl k x ∈ matrixIsometries Q) : x ∈ matrixIsometries Q₀ := by
  rw [mem_matrixIsometries_iff] at hx ⊢
  intro v
  apply Subtype.ext
  have h1 := hx (vecIncl k v)
  rw [matrixLinearEquiv_apply, mulVec_vecIncl, hext, hext] at h1
  rw [matrixLinearEquiv_apply]
  exact h1

theorem exists_ne_zero_of_nondeg (hd : 0 < d) (hnd : (polarBilin Q).Nondegenerate) :
    ∃ v, Q v ≠ 0 := by
  by_contra h
  push Not at h
  have hz : ∀ x y, polarBilin Q x y = 0 := fun x y => by
    rw [polarBilin_apply_apply]
    unfold QuadraticMap.polar
    rw [h, h, h]
    ring
  have h1 := hnd.1 (Pi.single ⟨0, hd⟩ 1) (fun y => hz _ y)
  have h2 := congrFun h1 ⟨0, hd⟩
  simp at h2

variable (Q) (σ : K ≃+* K) (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))

theorem fieldAutT_eq_self_iff (hext : IsExtension k Q₀ Q) (hσk : ∀ x, x ∈ k ↔ σ x = x) {p : ℕ}
    (hp : Odd p) (hσp : σ ^ p = 1) (hQne : ∃ v, Q v ≠ 0) (t : matrixProjectiveDerived Q) :
    fieldAutT Q σ hQσ t = t ↔ t ∈ subfieldFixedGroup k Q₀ Q := by
  constructor
  · obtain ⟨y, rfl⟩ := matrixProjectiveProjection_surjective Q t
    intro h
    rw [fieldAutT_mk] at h
    set w := matrixDerivedConjugation Q (fieldPair Q σ hQσ) y with hw
    have hwv : (w : GL (Fin d) K) = glFieldAut (Fin d) K σ y.val :=
      matrixDerivedConjugation_fieldPair_val Q σ hQσ y
    have h1 : y⁻¹ * w ∈ matrixDerivedScalars Q := by
      rw [matrixProjectiveProjection, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h
      exact QuotientGroup.eq.mp h.symm
    obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q _).mp h1
    have hwy : glFieldAut (Fin d) K σ y.val = y.val * GeneralLinearGroup.scalar (Fin d) c := by
      rw [← hwv]
      have : (GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) K) = y.val⁻¹ * w.val := hc
      rw [this]
      group
    have hiso : GeneralLinearGroup.scalar (Fin d) c ∈ matrixIsometries Q := by
      have : (GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) K) = y.val⁻¹ * w.val := hc
      rw [this]
      exact mul_mem (inv_mem (matrixDerived_le_isometries Q y.2))
        (matrixDerived_le_isometries Q w.2)
    obtain ⟨v, hv⟩ := hQne
    have hc2 : (c : K) * c = 1 := by
      have h2 := (mem_matrixIsometries_iff Q _).mp hiso v
      rw [matrixLinearEquiv_scalar, QuadraticMap.map_smul, smul_eq_mul] at h2
      exact mul_right_cancel₀ hv (by rw [one_mul]; exact h2)
    have hσc : σ (c : K) = c := by
      rcases mul_self_eq_one_iff.mp hc2 with h3 | h3 <;> simp [h3]
    have hSc : glFieldAut (Fin d) K σ (GeneralLinearGroup.scalar (Fin d) c) =
        GeneralLinearGroup.scalar (Fin d) c := by
      change glFieldEquiv (Fin d) σ _ = _
      rw [glFieldEquiv_scalar]
      congr 1
      exact Units.ext hσc
    have hS2 : glFieldAut (Fin d) K σ (glFieldAut (Fin d) K σ y.val) = y.val := by
      rw [hwy, map_mul, hwy, hSc, mul_assoc, ← map_mul]
      have hcc : c * c = 1 := Units.ext hc2
      rw [hcc, map_one, mul_one]
    have hSp : (glFieldAut (Fin d) K σ) ^ p = 1 := by rw [← map_pow, hσp, map_one]
    have hfix : glFieldAut (Fin d) K σ y.val = y.val :=
      apply_eq_of_sq_apply_eq (glFieldAut (Fin d) K σ) hp hSp hS2
    obtain ⟨x, hx⟩ := exists_glIncl_of_fixed k hσk hfix
    refine ⟨y, ?_, rfl⟩
    refine ⟨x, mem_isometries_of_glIncl k hext (hx ▸ matrixDerived_le_isometries Q y.2), hx⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, -, hx⟩ := hy
    rw [fieldAutT_mk]
    congr 1
    apply Subtype.ext
    have hxy : glIncl k x = y.val := hx
    rw [matrixDerivedConjugation_fieldPair_val, ← hxy, glFieldAut_glIncl k hσk]

end FixedGroup


section Structure

open CFSG.RankThree.Classical CFSG.RankThree.Classical2

variable {K : Type} [Field K] (k : Subfield K) {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

theorem three_le_of_totallySingular (hT₀ : ∃ U : Submodule k (Fin d → k),
    Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0) : 0 < d := by
  obtain ⟨U, hU, -⟩ := hT₀
  have := Submodule.finrank_le U
  rw [Module.finrank_fin_fun] at this
  omega

theorem matrix_simple_nonabelian {F : Type} [Field F] [Finite F] {Q' : QuadraticForm F (Fin d → F)}
    (hd : 0 < d) (hnd : (polarBilin Q').Nondegenerate)
    (hT : ∃ U : Submodule F (Fin d → F), Module.finrank F U = 3 ∧ ∀ u ∈ U, Q' u = 0) :
    IsSimpleGroup (matrixProjectiveDerived Q') ∧
      ∃ a b : matrixProjectiveDerived Q', a * b ≠ b * a := by
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ := orthogonal_high_Witt_derived_quotient_and_odd_lifts hnd hT
  have e := KCOrthogonalAut.coordBridge Q' hd
  refine ⟨e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnonab
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this

theorem center_matrix_eq_bot {F : Type} [Field F] [Finite F] {Q' : QuadraticForm F (Fin d → F)}
    (hd : 0 < d) (hnd : (polarBilin Q').Nondegenerate)
    (hT : ∃ U : Submodule F (Fin d → F), Module.finrank F U = 3 ∧ ∀ u ∈ U, Q' u = 0) :
    Subgroup.center (matrixProjectiveDerived Q') = ⊥ := by
  obtain ⟨hsimple, c, e, hce⟩ := matrix_simple_nonabelian hd hnd hT
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (matrixProjectiveDerived Q'))
    with h | h
  · exact h
  · exfalso
    exact hce (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top e) c)

@[expose] noncomputable def inclEquiv (hext : IsExtension k Q₀ Q) (hd : 0 < d) :
    matrixProjectiveDerived Q₀ ≃* ↥(subfieldDerivedImage k hext) :=
  MonoidHom.ofInjective (incl_injective k hext hd)

theorem subfieldDerivedImage_le (hext : IsExtension k Q₀ Q) :
    subfieldDerivedImage k hext ≤ subfieldFixedGroup k Q₀ Q := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨y, rfl⟩ := matrixProjectiveProjection_surjective Q₀ z
  rw [incl_mk]
  refine ⟨inclHom k hext y, ?_, rfl⟩
  exact ⟨y.1, matrixDerived_le_isometries Q₀ y.2, rfl⟩

theorem conj_mem_matrixDerived {x : GL (Fin d) k} (hx : x ∈ matrixIsometries Q₀) {z : GL (Fin d) k}
    (hz : z ∈ matrixDerived Q₀) : x * z * x⁻¹ ∈ matrixDerived Q₀ := by
  have hz' := hz
  rw [matrixDerived_eq_map_commutator] at hz'
  obtain ⟨z', hz'', hzz⟩ := hz'
  have hn : (commutator ↥(matrixIsometries Q₀)).Normal := inferInstance
  have h1 := hn.conj_mem z' hz'' ⟨x, hx⟩
  rw [matrixDerived_eq_map_commutator]
  refine ⟨_, h1, ?_⟩
  simp only [map_mul, map_inv, Subgroup.coe_subtype, hzz]

theorem subfieldDerivedImage_normal (hext : IsExtension k Q₀ Q) :
    ((subfieldDerivedImage k hext).subgroupOf (subfieldFixedGroup k Q₀ Q)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (subfieldDerivedImage_le k hext)]
  rintro _ n ⟨z, rfl⟩ ⟨y, hy, rfl⟩
  obtain ⟨z₀, rfl⟩ := matrixProjectiveProjection_surjective Q₀ z
  obtain ⟨x, hx, hxy⟩ := hy
  have hxy' : glIncl k x = y.val := hxy
  let z' : matrixDerived Q₀ := ⟨x * z₀.val * x⁻¹, conj_mem_matrixDerived k hx z₀.2⟩
  refine ⟨matrixProjectiveProjection Q₀ z', ?_⟩
  rw [incl_mk, incl_mk, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change glIncl k (x * z₀.val * x⁻¹) = y.val * glIncl k z₀.val * y.val⁻¹
  rw [map_mul, map_mul, map_inv, hxy']

theorem sq_mem_matrixDerived [Finite K] (hnd₀ : (polarBilin Q₀).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    {x : GL (Fin d) k} (hx : x ∈ matrixIsometries Q₀) : x * x ∈ matrixDerived Q₀ := by
  have : Finite k := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  obtain ⟨-, -, -, -, -, hsq, -⟩ := orthogonal_high_Witt_derived_quotient_and_odd_lifts hnd₀ hT₀
  have h1 := hsq (matrixLinearIso x) hx
  rw [pow_two, ← map_mul, ← KCOrthogonalAut.map_matrixDerived Q₀] at h1
  obtain ⟨z, hz, hzx⟩ := h1
  have : z = x * x := matrixLinearIso.injective hzx
  rwa [this] at hz

theorem fixedGroup_quotient_isPGroup [Finite K] (hext : IsExtension k Q₀ Q)
    (hnd₀ : (polarBilin Q₀).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    [((subfieldDerivedImage k hext).subgroupOf (subfieldFixedGroup k Q₀ Q)).Normal] :
    IsPGroup 2 (↥(subfieldFixedGroup k Q₀ Q) ⧸
      (subfieldDerivedImage k hext).subgroupOf (subfieldFixedGroup k Q₀ Q)) := by
  intro q
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨y, hy, hyn⟩ := n.2
  obtain ⟨x, hx, hxy⟩ : ∃ x ∈ matrixIsometries Q₀, glIncl k x = y.val := hy
  refine ⟨1, ?_⟩
  rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  let z : matrixDerived Q₀ := ⟨x * x, sq_mem_matrixDerived k hnd₀ hT₀ hx⟩
  refine ⟨matrixProjectiveProjection Q₀ z, ?_⟩
  rw [incl_mk]
  rw [Subgroup.coe_pow, ← hyn, ← map_pow]
  congr 1
  apply Subtype.ext
  change glIncl k (x * x) = y.val ^ 2
  rw [map_mul, hxy, pow_two]

end Structure


section Order

open CFSG.RankThree.Classical.SteinbergBY (matrixProjectiveConjugationHom_eq_one_iff)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (projectivePointAction)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (ActionProperties)

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K)) (σ : K ≃+* K)
  (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))

theorem fieldPair_val : (fieldPair Q σ hQσ).val = SemidirectProduct.inr σ := rfl

theorem fieldPair_pow_val (m : ℕ) :
    ((fieldPair Q σ hQσ) ^ m).val = SemidirectProduct.inr (σ ^ m) := by
  rw [Subgroup.coe_pow, fieldPair_val, ← map_pow]

theorem fieldPair_zpow_val (m : ℤ) :
    ((fieldPair Q σ hQσ) ^ m).val = SemidirectProduct.inr (σ ^ m) := by
  rw [Subgroup.coe_zpow, fieldPair_val, ← map_zpow]

theorem fieldAutT_pow_eq_one_iff (hnd : (polarBilin Q).Nondegenerate)
    (hS3 : ∃ S : Submodule K (Fin d → K), Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (hAP : ActionProperties Q (projectivePointAction Q)) (m : ℕ) :
    fieldAutT Q σ hQσ ^ m = 1 ↔ σ ^ m = 1 := by
  rw [fieldAutT, ← map_pow, matrixProjectiveConjugationHom_eq_one_iff Q hnd hS3 hAP,
    fieldPair_pow_val]
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro h
    exact ⟨h, 1, by rw [SemidirectProduct.left_inr, map_one]⟩

theorem orderOf_fieldAutT (hnd : (polarBilin Q).Nondegenerate)
    (hS3 : ∃ S : Submodule K (Fin d → K), Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (hAP : ActionProperties Q (projectivePointAction Q)) :
    orderOf (fieldAutT Q σ hQσ) = orderOf σ :=
  orderOf_eq_orderOf_iff.mpr (fieldAutT_pow_eq_one_iff Q σ hQσ hnd hS3 hAP)

end Order

end CFSG.RankThree.PartOne.KCOrthogonalSubfield
