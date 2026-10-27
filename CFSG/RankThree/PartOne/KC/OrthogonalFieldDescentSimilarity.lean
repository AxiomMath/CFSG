module

public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalDescent

section Quotient

variable {G G' : Type} [Group G] [Group G']

@[expose] def subgroupEquivOfMap (φ : G ≃* G') {H : Subgroup G} {H' : Subgroup G'}
    (hH : H.map φ.toMonoidHom = H') : H ≃* H' :=
  (φ.subgroupMap H).trans (MulEquiv.subgroupCongr hH)

theorem subgroupEquivOfMap_val (φ : G ≃* G') {H : Subgroup G} {H' : Subgroup G'}
    (hH : H.map φ.toMonoidHom = H') (y : H) : (subgroupEquivOfMap φ hH y : G') = φ y := rfl

theorem map_subgroupOf_equiv (φ : G ≃* G') {H Z : Subgroup G} {H' Z' : Subgroup G'}
    (hH : H.map φ.toMonoidHom = H') (hZ : Z.map φ.toMonoidHom = Z') :
    (Z.subgroupOf H).map (subgroupEquivOfMap φ hH).toMonoidHom = Z'.subgroupOf H' := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ Z := hy
    show φ y.val ∈ Z'
    rw [← hZ]
    exact Subgroup.mem_map_of_mem _ hy'
  · intro hx
    have hx' : (x : G') ∈ Z' := hx
    rw [← hZ] at hx'
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx'
    have hxH : (x : G') ∈ H.map φ.toMonoidHom := hH ▸ x.property
    obtain ⟨h, hh, hhx⟩ := Subgroup.mem_map.mp hxH
    have hzh : z = h := φ.injective (hzx.trans hhx.symm)
    subst hzh
    refine ⟨⟨z, hh⟩, hz, ?_⟩
    exact Subtype.ext hzx

noncomputable def quotientSubgroupOfEquiv (φ : G ≃* G') {H Z : Subgroup G} {H' Z' : Subgroup G'}
    [(Z.subgroupOf H).Normal] [(Z'.subgroupOf H').Normal]
    (hH : H.map φ.toMonoidHom = H') (hZ : Z.map φ.toMonoidHom = Z') :
    H ⧸ Z.subgroupOf H ≃* H' ⧸ Z'.subgroupOf H' :=
  QuotientGroup.congr (Z.subgroupOf H) (Z'.subgroupOf H') (subgroupEquivOfMap φ hH)
    (map_subgroupOf_equiv φ hH hZ)

theorem quotientSubgroupOfEquiv_mk (φ : G ≃* G') {H Z : Subgroup G} {H' Z' : Subgroup G'}
    [(Z.subgroupOf H).Normal] [(Z'.subgroupOf H').Normal]
    (hH : H.map φ.toMonoidHom = H') (hZ : Z.map φ.toMonoidHom = Z') (y : H) (y' : H')
    (hy : (y' : G') = φ y) :
    quotientSubgroupOfEquiv φ hH hZ (QuotientGroup.mk y) = QuotientGroup.mk y' := by
  have h := QuotientGroup.congr_mk (Z.subgroupOf H) (Z'.subgroupOf H')
    (subgroupEquivOfMap φ hH) (map_subgroupOf_equiv φ hH hZ) y
  refine h.trans ?_
  congr 1
  exact Subtype.ext hy.symm

theorem map_center_equiv (φ : G ≃* G) : (Subgroup.center G).map φ.toMonoidHom = Subgroup.center G
    := by
  ext x
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hx
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    have := hx (φ.symm g)
    have h2 := congrArg φ this
    simpa using h2
  · intro hx
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    have := hx (φ g)
    apply φ.injective
    simpa using this

end Quotient

section Abstract

variable {k : Type} [Field k] {V₀ W : Type} [AddCommGroup V₀] [Module k V₀] [AddCommGroup W]
  [Module k W]

@[expose] def linConj (S : V₀ ≃ₗ[k] W) : (V₀ ≃ₗ[k] V₀) ≃* (W ≃ₗ[k] W) where
  toFun g := S.symm.trans (g.trans S)
  invFun h := S.trans (h.trans S.symm)
  left_inv g := by
    ext v
    simp
  right_inv h := by
    ext w
    simp
  map_mul' g h := by
    ext w
    simp

theorem linConj_apply (S : V₀ ≃ₗ[k] W) (g : V₀ ≃ₗ[k] V₀) (w : W) :
    linConj S g w = S (g (S.symm w)) := rfl

theorem linConj_mem_orthogonalGroup_iff {Q₀ : QuadraticForm k V₀} {Q₁ : QuadraticForm k W}
    (S : V₀ ≃ₗ[k] W) (ν : kˣ) (hS : ∀ v, Q₁ (S v) = ν * Q₀ v) (g : V₀ ≃ₗ[k] V₀) :
    linConj S g ∈ TauCeti.QuadraticMap.orthogonalGroup Q₁ ↔
      g ∈ TauCeti.QuadraticMap.orthogonalGroup Q₀ := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  constructor
  · intro h v
    have h1 := h (S v)
    rw [linConj_apply, LinearEquiv.symm_apply_apply, hS, hS] at h1
    exact mul_left_cancel₀ ν.ne_zero h1
  · intro h w
    rw [linConj_apply]
    obtain ⟨v, rfl⟩ := S.surjective w
    rw [LinearEquiv.symm_apply_apply, hS, hS, h]

theorem map_orthogonalGroup {Q₀ : QuadraticForm k V₀} {Q₁ : QuadraticForm k W}
    (S : V₀ ≃ₗ[k] W) (ν : kˣ) (hS : ∀ v, Q₁ (S v) = ν * Q₀ v) :
    (TauCeti.QuadraticMap.orthogonalGroup Q₀).map (linConj S).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q₁ := by
  ext x
  rw [Subgroup.mem_map_equiv]
  have h := linConj_mem_orthogonalGroup_iff S ν hS ((linConj S).symm x)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem map_scalars (S : V₀ ≃ₗ[k] W) :
    (CFSG.ClassicalGroups.Orthogonal.scalars k V₀).map (linConj S).toMonoidHom =
      CFSG.ClassicalGroups.Orthogonal.scalars k W := by
  ext x
  rw [Subgroup.mem_map_equiv, CFSG.ClassicalGroups.Orthogonal.mem_scalars,
    CFSG.ClassicalGroups.Orthogonal.mem_scalars]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun w => ?_⟩
    have h1 := hc (S.symm w)
    change S.symm (x (S (S.symm w))) = c • S.symm w at h1
    rw [LinearEquiv.apply_symm_apply] at h1
    calc x w = S (S.symm (x w)) := (S.apply_symm_apply _).symm
      _ = S (c • S.symm w) := by rw [h1]
      _ = c • w := by rw [map_smul, LinearEquiv.apply_symm_apply]
  · rintro ⟨c, hc⟩
    refine ⟨c, fun v => ?_⟩
    change S.symm (x (S v)) = c • v
    rw [hc, map_smul, LinearEquiv.symm_apply_apply]

theorem map_orthDerived {Q₀ : QuadraticForm k V₀} {Q₁ : QuadraticForm k W}
    (S : V₀ ≃ₗ[k] W) (ν : kˣ) (hS : ∀ v, Q₁ (S v) = ν * Q₀ v) :
    (CFSG.RankThree.Classical2.orthDerived Q₀).map (linConj S).toMonoidHom =
      CFSG.RankThree.Classical2.orthDerived Q₁ := by
  rw [CFSG.RankThree.Classical2.orthDerived, CFSG.RankThree.Classical2.orthDerived,
    Subgroup.map_commutator, map_orthogonalGroup S ν hS]

noncomputable def projOrthDerivedEquiv {Q₀ : QuadraticForm k V₀} {Q₁ : QuadraticForm k W}
    (S : V₀ ≃ₗ[k] W) (ν : kˣ) (hS : ∀ v, Q₁ (S v) = ν * Q₀ v) :
    CFSG.RankThree.Classical2.ProjOrthDerived Q₀ ≃*
      CFSG.RankThree.Classical2.ProjOrthDerived Q₁ :=
  quotientSubgroupOfEquiv (linConj S) (map_orthDerived S ν hS) (map_scalars S)

end Abstract

section Matrix

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Matrix
  CFSG.ComponentClassification.CatalogueBHigherLinearField

variable {K : Type} [Field K] {d : ℕ}

theorem matrixLinearIso_conj (S A : GL (Fin d) K) :
    matrixLinearIso (S * A * S⁻¹) = linConj (matrixLinearIso S) (matrixLinearIso A) := by
  ext w
  simp [linConj_apply, map_mul, map_inv, LinearEquiv.mul_apply]

theorem matrix_map_isometries (Q Q' : QuadraticForm K (Fin d → K)) (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' (matrixLinearIso S v) = ν * Q v) :
    (matrixIsometries Q).map (MulAut.conj S).toMonoidHom = matrixIsometries Q' := by
  ext x
  rw [Subgroup.mem_map_equiv]
  change matrixLinearIso ((MulAut.conj S).symm x) ∈ TauCeti.QuadraticMap.orthogonalGroup Q ↔
    matrixLinearIso x ∈ TauCeti.QuadraticMap.orthogonalGroup Q'
  have h := linConj_mem_orthogonalGroup_iff (matrixLinearIso S) ν hS
    (matrixLinearIso ((MulAut.conj S).symm x))
  have h1 : linConj (matrixLinearIso S) (matrixLinearIso ((MulAut.conj S).symm x)) =
      matrixLinearIso x := by
    rw [← matrixLinearIso_conj]
    congr 1
    exact MulEquiv.apply_symm_apply (MulAut.conj S) x
  rw [h1] at h
  exact h.symm

theorem matrix_map_scalars (S : GL (Fin d) K) :
    (matrixScalars d K).map (MulAut.conj S).toMonoidHom = matrixScalars d K := by
  rw [matrixScalars_eq_center]
  exact map_center_equiv _

theorem matrix_map_derived (Q Q' : QuadraticForm K (Fin d → K)) (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, Q' (matrixLinearIso S v) = ν * Q v) :
    (matrixDerived Q).map (MulAut.conj S).toMonoidHom = matrixDerived Q' := by
  rw [matrixDerived, matrixDerived, Subgroup.map_commutator,
    matrix_map_isometries Q Q' S ν hS]

noncomputable def matrixProjectiveSimilarityEquiv (Q Q' : QuadraticForm K (Fin d → K))
    (S : GL (Fin d) K) (ν : Kˣ) (hS : ∀ v, Q' (matrixLinearIso S v) = ν * Q v) :
    matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q' :=
  quotientSubgroupOfEquiv (MulAut.conj S) (matrix_map_derived Q Q' S ν hS) (matrix_map_scalars S)

theorem matrixProjectiveSimilarityEquiv_mk (Q Q' : QuadraticForm K (Fin d → K)) (S : GL (Fin d) K)
    (ν : Kˣ) (hS : ∀ v, Q' (matrixLinearIso S v) = ν * Q v) (A : matrixDerived Q)
    (B : matrixDerived Q') (hB : B.val = S * A.val * S⁻¹) :
    matrixProjectiveSimilarityEquiv Q Q' S ν hS (matrixProjectiveProjection Q A) =
      matrixProjectiveProjection Q' B :=
  quotientSubgroupOfEquiv_mk _ _ _ A B (by rw [hB]; rfl)

theorem exists_conj_mem_matrixDerived (Q Q' : QuadraticForm K (Fin d → K)) (S : GL (Fin d) K)
    (ν : Kˣ) (hS : ∀ v, Q' (matrixLinearIso S v) = ν * Q v) (A : matrixDerived Q) :
    ∃ B : matrixDerived Q', B.val = S * A.val * S⁻¹ := by
  have h : S * A.val * S⁻¹ ∈ matrixDerived Q' := by
    rw [← matrix_map_derived Q Q' S ν hS]
    exact Subgroup.mem_map_of_mem _ A.property
  exact ⟨⟨_, h⟩, rfl⟩

theorem matrixProjectiveSimilarityEquiv_conj (Q Q' : QuadraticForm K (Fin d → K))
    (S : GL (Fin d) K) (ν : Kˣ) (hS : ∀ v, Q' (matrixLinearIso S v) = ν * Q v)
    (U : similarityPairs Q) (g' : similarityPairs Q') (hl : g'.val.left = 1)
    (hr : g'.val.right = U.val.right)
    (hSU : S * U.val.left = glFieldAut (Fin d) K U.val.right S)
    (x : matrixProjectiveDerived Q) :
    matrixProjectiveSimilarityEquiv Q Q' S ν hS (matrixProjectiveConjugationHom Q U x) =
      matrixProjectiveConjugationHom Q' g' (matrixProjectiveSimilarityEquiv Q Q' S ν hS x) := by
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q x
  obtain ⟨B, hB⟩ := exists_conj_mem_matrixDerived Q Q' S ν hS A
  rw [matrixProjectiveSimilarityEquiv_mk Q Q' S ν hS A B hB]
  change matrixProjectiveSimilarityEquiv Q Q' S ν hS (matrixProjectiveConjugation Q U _) =
    matrixProjectiveConjugation Q' g' _
  rw [matrixProjectiveConjugation_mk, matrixProjectiveConjugation_mk]
  obtain ⟨B', hB'⟩ := exists_conj_mem_matrixDerived Q Q' S ν hS (matrixDerivedConjugation Q U A)
  rw [matrixProjectiveSimilarityEquiv_mk Q Q' S ν hS _ B' hB']
  congr 1
  apply Subtype.ext
  rw [hB', matrixDerivedConjugation_val, matrixDerivedConjugation_val, hl, hr, hB]
  simp only [one_mul, inv_one, mul_one, map_mul, map_inv]
  rw [← hSU]
  group

end Matrix

end CFSG.RankThree.PartOne.KCOrthogonalDescent
