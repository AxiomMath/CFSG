module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataEmbedding
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmegaAnisoNeg
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmegaAnisoWeights

public section

namespace CFSG.LocalAnalysis.WeakClosure81.POmegaOuter

open Subgroup Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

private lemma matrixLinearIso_scalar' {K : Type} [Field K] {d : ℕ} (c : Kˣ) :
    matrixLinearIso (GeneralLinearGroup.scalar (Fin d) c) =
      c • (1 : (Fin d → K) ≃ₗ[K] (Fin d → K)) := by
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.smul_apply]
  change matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) c) v = (c : K) • v
  rw [matrixLinearEquiv_apply]
  funext i
  simp [GeneralLinearGroup.coe_scalar, Matrix.mulVec_diagonal]

private theorem matrixProjectiveConjugationHom_derivedInclusion' {K : Type} [Field K]
    {d : ℕ} (Q : QuadraticForm K (Fin d → K)) (A : matrixDerived Q) :
    matrixProjectiveConjugationHom Q (matrixDerivedInclusion Q A) =
      MulAut.conj (matrixProjectiveProjection Q A) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨B, rfl⟩ := matrixProjectiveProjection_surjective Q x
  change matrixProjectiveConjugation Q _ (matrixProjectiveProjection Q B) = _
  rw [matrixProjectiveConjugation_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

private theorem matrixProjectiveConjugationHom_eq_of_left_eq_mul_scalar' {K : Type}
    [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {g h : similarityPairs Q}
    (c : Kˣ) (hleft : g.val.left = h.val.left * GeneralLinearGroup.scalar (Fin d) c)
    (hright : g.val.right = h.val.right) :
    matrixProjectiveConjugationHom Q g = matrixProjectiveConjugationHom Q h := by
  have hc : ∀ X : GL (Fin d) K, X * GeneralLinearGroup.scalar (Fin d) c =
      GeneralLinearGroup.scalar (Fin d) c * X := by
    intro X
    have hmem : GeneralLinearGroup.scalar (Fin d) c ∈ Subgroup.center (GL (Fin d) K) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    exact Subgroup.mem_center_iff.mp hmem X
  have hD : ∀ B, matrixDerivedConjugation Q g B = matrixDerivedConjugation Q h B := by
    intro B
    apply Subtype.ext
    rw [matrixDerivedConjugation_val, matrixDerivedConjugation_val, hleft, hright]
    set s := GeneralLinearGroup.scalar (Fin d) c
    set X := CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin d) K
      h.val.right B.val
    calc h.val.left * s * X * (h.val.left * s)⁻¹
        = h.val.left * (X * s) * s⁻¹ * h.val.left⁻¹ := by rw [hc X]; group
      _ = h.val.left * X * h.val.left⁻¹ := by group
  apply MulEquiv.ext
  intro x
  obtain ⟨B, rfl⟩ := matrixProjectiveProjection_surjective Q x
  change matrixProjectiveConjugation Q g (matrixProjectiveProjection Q B) =
    matrixProjectiveConjugation Q h (matrixProjectiveProjection Q B)
  rw [matrixProjectiveConjugation_mk, matrixProjectiveConjugation_mk, hD]

theorem mem_conj_range_of_isometric_lifts (h2 : (2 : K) ≠ 0) (hd7 : 7 ≤ d) (hd8 : d ≤ 8)
    (ga gb : similarityPairs Q) (hra : ga.val.right = 1) (hrb : gb.val.right = 1) {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hA2 : ∀ v, coordinateSemilinearMap ga.val (coordinateSemilinearMap ga.val v) = (a * a) • v)
    (hB2 : ∀ v, coordinateSemilinearMap gb.val (coordinateSemilinearMap gb.val v) = (b * b) • v)
    (hAsa : ∀ u w, polar Q (coordinateSemilinearMap ga.val u) w =
      polar Q u (coordinateSemilinearMap ga.val w))
    (hBsa : ∀ u w, polar Q (coordinateSemilinearMap gb.val u) w =
      polar Q u (coordinateSemilinearMap gb.val w))
    (hAB : ∀ v, coordinateSemilinearMap ga.val (coordinateSemilinearMap gb.val v) =
      coordinateSemilinearMap gb.val (coordinateSemilinearMap ga.val v))
    (hanis : ∀ v, (coordinateSemilinearMap ga.val v = a • v ∨
        coordinateSemilinearMap ga.val v = -(a • v)) →
      (coordinateSemilinearMap gb.val v = b • v ∨
        coordinateSemilinearMap gb.val v = -(b • v)) →
      Q v = 0 → v = 0) :
    matrixProjectiveConjugationHom Q ga ∈
      (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range := by
  have hga_inl : ga.val = SemidirectProduct.inl ga.val.left :=
    SemidirectProduct.ext rfl hra
  have hgb_inl : gb.val = SemidirectProduct.inl gb.val.left :=
    SemidirectProduct.ext rfl hrb
  have hLa : ∀ v, matrixLinearEquiv ga.val.left v = coordinateSemilinearMap ga.val v := by
    intro v
    rw [hga_inl]
    exact (coordinateSemilinearMap_inl (A := ga.val.left) v).symm
  have hLb : ∀ v, matrixLinearEquiv gb.val.left v = coordinateSemilinearMap gb.val v := by
    intro v
    rw [hgb_inl]
    exact (coordinateSemilinearMap_inl (A := gb.val.left) v).symm
  let ua : Kˣ := Units.mk0 a ha
  let ub : Kˣ := Units.mk0 b hb
  let La : (Fin d → K) ≃ₗ[K] (Fin d → K) := matrixLinearEquiv ga.val.left
  let Lb : (Fin d → K) ≃ₗ[K] (Fin d → K) := matrixLinearEquiv gb.val.left
  let A0 : (Fin d → K) ≃ₗ[K] (Fin d → K) := ua⁻¹ • La
  let B0 : (Fin d → K) ≃ₗ[K] (Fin d → K) := ub⁻¹ • Lb
  have hA0 : ∀ v, A0 v = a⁻¹ • La v := by
    intro v
    simp [A0, ua]
  have hB0 : ∀ v, B0 v = b⁻¹ • Lb v := by
    intro v
    simp [B0, ub]
  have hA2' : ∀ v, A0 (A0 v) = v := by
    intro v
    rw [hA0 (A0 v), hA0 v, map_smul, hLa (La v), hLa v, hA2]
    rw [smul_smul, smul_smul]
    have h1 : a⁻¹ * a⁻¹ * (a * a) = 1 := by field_simp
    rw [h1, one_smul]
  have hB2' : ∀ v, B0 (B0 v) = v := by
    intro v
    rw [hB0 (B0 v), hB0 v, map_smul, hLb (Lb v), hLb v, hB2]
    rw [smul_smul, smul_smul]
    have h1 : b⁻¹ * b⁻¹ * (b * b) = 1 := by field_simp
    rw [h1, one_smul]
  have hAsa' : ∀ u w, polar Q (La u) w = polar Q u (La w) := by
    intro u w
    rw [hLa u, hLa w]
    exact hAsa u w
  have hBsa' : ∀ u w, polar Q (Lb u) w = polar Q u (Lb w) := by
    intro u w
    rw [hLb u, hLb w]
    exact hBsa u w
  have hLa2 : ∀ w, La (La w) = (a * a) • w := by
    intro w
    rw [hLa (La w), hLa w, hA2 w]
  have hLb2 : ∀ w, Lb (Lb w) = (b * b) • w := by
    intro w
    rw [hLb (Lb w), hLb w, hB2 w]
  have hBisoA : ∀ u w, polar Q (A0 u) (A0 w) = polar Q u w := by
    intro u w
    rw [hA0 u, hA0 w, polar_smul_left_eq, polar_smul_right_eq, hAsa' u (La w),
      hLa2 w, polar_smul_right_eq]
    field_simp
  have hBisoB : ∀ u w, polar Q (B0 u) (B0 w) = polar Q u w := by
    intro u w
    rw [hB0 u, hB0 w, polar_smul_left_eq, polar_smul_right_eq, hBsa' u (Lb w),
      hLb2 w, polar_smul_right_eq]
    field_simp
  have hAQ' : ∀ v, Q (A0 v) = Q v := by
    intro v
    have h := hBisoA v v
    rw [polar_self_eq_two_mul, polar_self_eq_two_mul] at h
    exact mul_left_cancel₀ h2 h
  have hBQ' : ∀ v, Q (B0 v) = Q v := by
    intro v
    have h := hBisoB v v
    rw [polar_self_eq_two_mul, polar_self_eq_two_mul] at h
    exact mul_left_cancel₀ h2 h
  have hAB' : ∀ v, A0 (B0 v) = B0 (A0 v) := by
    intro v
    rw [hA0 (B0 v), hB0 v, hB0 (A0 v), hA0 v, map_smul, map_smul, hLa (Lb v),
      hLb (La v), hLa v, hLb v, hAB]
    rw [smul_smul, smul_smul]
    congr 1
    ring
  have hA0_spec : ∀ v, A0 v = v ↔ La v = a • v := by
    intro v
    rw [hA0 v]
    constructor
    · intro h
      have := congrArg (fun x => a • x) h
      simpa [smul_smul, ha] using this
    · intro h
      rw [h, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hA0_neg : ∀ v, A0 v = -v ↔ La v = -(a • v) := by
    intro v
    rw [hA0 v]
    constructor
    · intro h
      have := congrArg (fun x => a • x) h
      simpa [smul_smul, ha] using this
    · intro h
      rw [h, smul_neg, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hB0_spec : ∀ v, B0 v = v ↔ Lb v = b • v := by
    intro v
    rw [hB0 v]
    constructor
    · intro h
      have := congrArg (fun x => b • x) h
      simpa [smul_smul, hb] using this
    · intro h
      rw [h, smul_smul, inv_mul_cancel₀ hb, one_smul]
  have hB0_neg : ∀ v, B0 v = -v ↔ Lb v = -(b • v) := by
    intro v
    rw [hB0 v]
    constructor
    · intro h
      have := congrArg (fun x => b • x) h
      simpa [smul_smul, hb] using this
    · intro h
      rw [h, smul_neg, smul_smul, inv_mul_cancel₀ hb, one_smul]
  have hanis' : ∀ v, (A0 v = v ∨ A0 v = -v) → (B0 v = v ∨ B0 v = -v) → Q v = 0 → v = 0 := by
    intro v hA hB hQ
    apply hanis v
    · rcases hA with h | h
      · exact Or.inl ((hLa v).symm.trans ((hA0_spec v).mp h))
      · exact Or.inr ((hLa v).symm.trans ((hA0_neg v).mp h))
    · rcases hB with h | h
      · exact Or.inl ((hLb v).symm.trans ((hB0_spec v).mp h))
      · exact Or.inr ((hLb v).symm.trans ((hB0_neg v).mp h))
    · exact hQ
  have hd7' : 7 ≤ Module.finrank K (Fin d → K) := by rwa [Module.finrank_fin_fun]
  have hd8' : Module.finrank K (Fin d → K) ≤ 8 := by rwa [Module.finrank_fin_fun]
  obtain ⟨ε, hε, P₁, P₂, hP₁, hP₂, ha₁, ha₂, h₁₂, hneg, hpos⟩ :=
    exists_aniso_planes_of_commuting_involutions (Q := Q) h2 hd7' hd8'
      (A := (A0 : (Fin d → K) →ₗ[K] (Fin d → K)))
      (B := (B0 : (Fin d → K) →ₗ[K] (Fin d → K)))
      hA2' hB2' hAQ' hBQ' hAB' hanis'
  have hε0 : ε ≠ 0 := by
    rcases hε with h | h <;> rw [h] <;> norm_num
  let uε : Kˣ := Units.mk0 ε hε0
  let T : (Fin d → K) ≃ₗ[K] (Fin d → K) := uε • A0
  have hT_apply : ∀ x, T x = ε • A0 x := by
    intro x
    simp [T, uε]
  have hTmem : T ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    mem_commutator_of_neg_on_aniso_planes (Q := Q) h2 hP₁ hP₂ ha₁ ha₂ h₁₂ T
      (fun x hx => by rw [hT_apply]; exact hneg x hx)
      (fun x hx => by rw [hT_apply]; exact hpos x hx)
  have hmap : (matrixIsometries Q).map matrixLinearIso.toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [matrixIsometries]
    exact Subgroup.map_comap_eq_self_of_surjective matrixLinearIso.surjective _
  have hTmap : T ∈ (matrixDerived Q).map matrixLinearIso.toMonoidHom := by
    rw [matrixDerived, Subgroup.map_commutator, hmap]
    exact hTmem
  obtain ⟨M, hMmem, hMT⟩ := Subgroup.mem_map.mp hTmap
  let M' : matrixDerived Q := ⟨M, hMmem⟩
  let g' : similarityPairs Q := matrixDerivedInclusion Q M'
  have hMT' : matrixLinearIso M = (uε * ua⁻¹) • matrixLinearIso ga.val.left := by
    rw [show matrixLinearIso M = T from hMT]
    change uε • (ua⁻¹ • La) = (uε * ua⁻¹) • matrixLinearIso ga.val.left
    rw [show matrixLinearIso ga.val.left = La from rfl]
    have hsmul : uε • (ua⁻¹ • La) = (uε * ua⁻¹) • La := by
      ext v
      simp [LinearEquiv.smul_apply, mul_assoc]
    exact hsmul
  let c : Kˣ := (uε * ua⁻¹)⁻¹
  have hc_inv : c⁻¹ = uε * ua⁻¹ := inv_inv _
  have hMT'' : matrixLinearIso M = c⁻¹ • matrixLinearIso ga.val.left := by
    rw [hc_inv, hMT']
  have hleft : ga.val.left = M * GeneralLinearGroup.scalar (Fin d) c := by
    apply matrixLinearIso.injective
    rw [map_mul, matrixLinearIso_scalar', hMT'',
      show matrixLinearIso ga.val.left = La from rfl]
    ext v
    simp [LinearEquiv.smul_apply]
  have hright : ga.val.right = g'.val.right := by
    rw [hra]
    rfl
  have hκ : matrixProjectiveConjugationHom Q ga = matrixProjectiveConjugationHom Q g' :=
    matrixProjectiveConjugationHom_eq_of_left_eq_mul_scalar' c hleft hright
  rw [hκ, matrixProjectiveConjugationHom_derivedInclusion']
  exact ⟨matrixProjectiveProjection Q M', rfl⟩

end CFSG.LocalAnalysis.WeakClosure81.POmegaOuter
