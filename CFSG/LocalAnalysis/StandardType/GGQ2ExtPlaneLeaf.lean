module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtPlanePos
public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneChain
public import CFSG.LocalAnalysis.StandardType.GGQ2InLCoverFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCatalogue

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module PlaneRaw

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

namespace PlaneRaw

private theorem l08tpo1_zmod3_eq (a : F) : a = 0 ∨ a = 1 ∨ a = -1 := by
  decide +revert

private theorem l08tpo1_span_smul_singleton {t : ℕ} {s : F} (hs : s ≠ 0) (x : V t) :
    Submodule.span F {s • x} = Submodule.span F {x} :=
  Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hs) x

private def l08tpo1_globalNeg (t : ℕ) : V t ≃ₗ[F] V t :=
  LinearEquiv.piCongrRight fun _ => LinearEquiv.neg F

private theorem l08tpo1_globalNeg_apply {t : ℕ} (v : V t) :
    l08tpo1_globalNeg t v = -v := by
  funext i
  simp [l08tpo1_globalNeg, Pi.neg_apply]

private theorem l08tpo1_globalNeg_mul_self (t : ℕ) :
    l08tpo1_globalNeg t * l08tpo1_globalNeg t = 1 := by
  ext v
  simp only [LinearEquiv.mul_apply, l08tpo1_globalNeg_apply]
  simp

private theorem l08tpo1_globalNeg_comm {t : ℕ} (s : V t ≃ₗ[F] V t) :
    l08tpo1_globalNeg t * s = s * l08tpo1_globalNeg t := by
  ext v
  simp only [LinearEquiv.mul_apply, l08tpo1_globalNeg_apply, map_neg]

private theorem l08tpo1_globalNeg_inv (t : ℕ) :
    (l08tpo1_globalNeg t)⁻¹ = l08tpo1_globalNeg t :=
  inv_eq_of_mul_eq_one_right (l08tpo1_globalNeg_mul_self t)

private theorem l08tpo1_orient_smul_neg {t : ℕ} {e : V t} (he : ∀ i, e i ≠ 0) :
    orientEquiv t ((-1 : F) • e) = l08tpo1_globalNeg t * orientEquiv t e := by
  ext v i
  rcases l08tpo1_zmod3_eq (e i) with h | h | h
  · exact absurd h (he i)
  · have h1 : (1 : F) ≠ -1 := by decide
    simp [orientEquiv, l08tpo1_globalNeg, LinearEquiv.mul_apply, h, h1]
  · have h2 : (-1 : F) ≠ 1 := by decide
    simp [orientEquiv, l08tpo1_globalNeg, LinearEquiv.mul_apply, h, h2]

private theorem l08tpo1_swapTwist_negSmul {t : ℕ} {e : V t} (he : ∀ i, e i ≠ 0)
    (i j : Fin t) :
    swapTwist t ((-1 : F) • e) i j = swapTwist t e i j := by
  have hcomm : l08tpo1_globalNeg t * swapEquiv t i j =
      swapEquiv t i j * l08tpo1_globalNeg t := l08tpo1_globalNeg_comm (swapEquiv t i j)
  have hgg : l08tpo1_globalNeg t * l08tpo1_globalNeg t = 1 := l08tpo1_globalNeg_mul_self t
  have hinv : (l08tpo1_globalNeg t)⁻¹ = l08tpo1_globalNeg t := l08tpo1_globalNeg_inv t
  simp only [swapTwist]
  rw [l08tpo1_orient_smul_neg he]
  rw [mul_inv_rev, hinv]
  calc (orientEquiv t e)⁻¹ * l08tpo1_globalNeg t * swapEquiv t i j *
        (l08tpo1_globalNeg t * orientEquiv t e)
      = (orientEquiv t e)⁻¹ * (l08tpo1_globalNeg t * swapEquiv t i j) *
          (l08tpo1_globalNeg t * orientEquiv t e) := by group
    _ = (orientEquiv t e)⁻¹ * (swapEquiv t i j * l08tpo1_globalNeg t) *
          (l08tpo1_globalNeg t * orientEquiv t e) := by rw [hcomm]
    _ = (orientEquiv t e)⁻¹ * swapEquiv t i j *
          (l08tpo1_globalNeg t * l08tpo1_globalNeg t) * orientEquiv t e := by group
    _ = (orientEquiv t e)⁻¹ * swapEquiv t i j * 1 * orientEquiv t e := by rw [hgg]
    _ = (orientEquiv t e)⁻¹ * swapEquiv t i j * orientEquiv t e := by group

private theorem l08tpo1_twistedPerm_neg {t : ℕ} {e : V t} (he : ∀ i, e i ≠ 0) :
    twistedPermGroupOn t ((-1 : F) • e) = twistedPermGroupOn t e := by
  apply le_antisymm
  · rw [twistedPermGroupOn, twistedPermGroupOn]
    rw [Subgroup.closure_le]
    rintro T ⟨i, j, _, _, rfl⟩
    rw [l08tpo1_swapTwist_negSmul he i j]
    exact Subgroup.subset_closure ⟨i, j, he i, he j, rfl⟩
  · rw [twistedPermGroupOn, twistedPermGroupOn]
    rw [Subgroup.closure_le]
    rintro T ⟨i, j, h1, h2, rfl⟩
    rw [← l08tpo1_swapTwist_negSmul he i j]
    exact Subgroup.subset_closure ⟨i, j,
      by simpa [Pi.smul_apply, smul_eq_mul] using neg_ne_zero.mpr h1,
      by simpa [Pi.smul_apply, smul_eq_mul] using neg_ne_zero.mpr h2, rfl⟩

end PlaneRaw

theorem PlaneRaw.extKey_ne_zero {t : ℕ} {b : Fin t} {e' : V t} (he'b : e' b = 0)
    (he'i : ∀ i, i ≠ b → e' i ≠ 0) {ε σ : F} (hε : ε ≠ 0) (hσ : σ ≠ 0) (i : Fin t) :
    (ε • (e' + σ • unitVec t b)) i ≠ 0 := by
  rw [Pi.smul_apply]
  by_cases hi : i = b
  · subst i
    have h1 : (e' + σ • unitVec t b) b = σ := by
      simp [unitVec, he'b, smul_eq_mul]
    rw [h1, smul_eq_mul]
    exact mul_ne_zero hε hσ
  · have h1 : (e' + σ • unitVec t b) i = e' i := by
      simp [unitVec, Pi.single_apply, hi, smul_eq_mul]
    rw [h1, smul_eq_mul]
    exact mul_ne_zero hε (he'i i hi)

theorem PlaneRaw.extKey_sub_ne_zero {t : ℕ} {b : Fin t} {e' : V t} (he'b : e' b = 0)
    (he'i : ∀ i, i ≠ b → e' i ≠ 0) {ε σ : F} (hε : ε ≠ 0) (hσ : σ ≠ 0) (i : Fin t) :
    (ε • (e' - σ • unitVec t b)) i ≠ 0 := by
  rw [Pi.smul_apply]
  by_cases hi : i = b
  · subst i
    have h1 : (e' - σ • unitVec t b) b = -σ := by
      simp [unitVec, he'b, smul_eq_mul]
    rw [h1, smul_eq_mul, mul_neg]
    exact neg_ne_zero.mpr (mul_ne_zero hε hσ)
  · have h1 : (e' - σ • unitVec t b) i = e' i := by
      simp [unitVec, Pi.single_apply, hi, smul_eq_mul]
    rw [h1, smul_eq_mul]
    exact mul_ne_zero hε (he'i i hi)

theorem PlaneRaw.LeafModelOn.congr_span {t : ℕ} {Na Nb : Subgroup (V t ≃ₗ[F] V t)}
    {vx z vx' z' : V t} (h : LeafModelOn t Na Nb vx z)
    (hvx : Submodule.span F {vx'} = Submodule.span F {vx})
    (hz : Submodule.span F {z'} = Submodule.span F {z}) : LeafModelOn t Na Nb vx' z' := by
  obtain ⟨W, h1, h2, h3, h4, h5⟩ := h
  exact ⟨W, h1, h2, fun v => (h3 v).trans (by rw [hvx]),
    fun v => (h4 v).trans (by rw [hz]), h5⟩

theorem PlaneRaw.twistedPermGroupOn_smul {t : ℕ} {e : V t} (he : ∀ i, e i ≠ 0) {ε : F}
    (hε : ε ≠ 0) : twistedPermGroupOn t (ε • e) = twistedPermGroupOn t e := by
  rcases l08tpo1_zmod3_eq ε with h | h | h
  · exact absurd h hε
  · subst h
    rw [one_smul]
  · subst h
    exact l08tpo1_twistedPerm_neg he

theorem PlaneRaw.normalizerOf_zero_erase_signed {kd : PlaneKind} (hkd : kd ≠ .orthogonal 0)
    {t : ℕ} (ht : 4 ≤ t) (c : Fin t) :
    PlaneRaw.normalizerOf kd t (.zero (Finset.univ.erase c)) = signedPermGroupOn t (Finset.univ.erase c) := by
  have hcard : (Finset.univ.erase c).card = t - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  have hne2 : (Finset.univ.erase c).card ≠ 2 := by omega
  cases kd with
  | linear ε => rfl
  | symplectic =>
      rw [PlaneRaw.normalizerOf, if_neg hne2]
  | orthogonal δ =>
      have hδ : δ.val ≠ 0 := by
        intro h
        exact hkd (by
          apply congrArg PlaneKind.orthogonal
          exact Fin.ext (by simpa using h))
      rw [PlaneRaw.normalizerOf, if_neg hδ]

theorem PlaneRaw.normalizerOf_zero_even {t : ℕ} (S : Finset (Fin t)) :
    PlaneRaw.normalizerOf (.orthogonal 0) t (.zero S) = evenSignedPermGroupOn t S := by
  rfl

theorem PlaneRaw.normalizerOf_extension (kd : PlaneKind) {t : ℕ} (e : V t) :
    PlaneRaw.normalizerOf kd t (.extension e) = twistedPermGroupOn t e :=
  rfl

theorem extLeaf_A2_signed (hLS : LeafModelSigned) {kd : PlaneKind} (hkd : kd ≠ .orthogonal 0)
    {t : ℕ} (ht : 4 ≤ t) {vx z : V t} {ℓ j k : Code t} {U : Submodule F (V t)}
    (h : ExtShapeA2 vx ℓ U j z k) : InLLeafAt (planeEntry kd t) vx z ℓ k := by
  obtain ⟨a, e', s, β, σ, ε, hs, hβ, hσ, hε, he'a, he'i, hvx, hℓ, _hj, _hU, hz, hk⟩ := h
  subst hvx; subst hℓ; subst hz; subst hk
  have he : ∀ i, (ε • (e' + σ • unitVec t a)) i ≠ 0 :=
    extKey_ne_zero he'a he'i hε hσ
  have hmodel := (hLS t ht (ε • (e' + σ • unitVec t a)) he a).swap
  change LeafModelOn t (PlaneRaw.normalizerOf kd t (.zero (Finset.univ.erase a)))
    (PlaneRaw.normalizerOf kd t (.extension (ε • (e' + σ • unitVec t a))))
    (s • unitVec t a) (β • (e' + σ • unitVec t a))
  rw [normalizerOf_zero_erase_signed hkd ht a,
    normalizerOf_extension kd (ε • (e' + σ • unitVec t a))]
  refine hmodel.congr_span ?_ ?_
  · simpa [unitVec] using l08tpo1_span_smul_singleton hs (unitVec t a)
  · exact (l08tpo1_span_smul_singleton hβ (e' + σ • unitVec t a)).trans
      (l08tpo1_span_smul_singleton hε (e' + σ • unitVec t a)).symm

theorem extLeaf_A2_even (hLE : LeafModelEvenSigned) {t : ℕ} (ht : 4 ≤ t) {vx z : V t}
    {ℓ j k : Code t} {U : Submodule F (V t)} (h : ExtShapeA2 vx ℓ U j z k) :
    InLLeafAt (planeEntry (.orthogonal 0) t) vx z ℓ k := by
  obtain ⟨a, e', s, β, σ, ε, hs, hβ, hσ, hε, he'a, he'i, hvx, hℓ, _hj, _hU, hz, hk⟩ := h
  subst hvx; subst hℓ; subst hz; subst hk
  have he : ∀ i, (ε • (e' + σ • unitVec t a)) i ≠ 0 :=
    extKey_ne_zero he'a he'i hε hσ
  have hmodel := (hLE t ht (ε • (e' + σ • unitVec t a)) he a).swap
  change LeafModelOn t (PlaneRaw.normalizerOf (.orthogonal 0) t (.zero (Finset.univ.erase a)))
    (PlaneRaw.normalizerOf (.orthogonal 0) t (.extension (ε • (e' + σ • unitVec t a))))
    (s • unitVec t a) (β • (e' + σ • unitVec t a))
  rw [normalizerOf_zero_even (Finset.univ.erase a),
    normalizerOf_extension (.orthogonal 0) (ε • (e' + σ • unitVec t a))]
  refine hmodel.congr_span ?_ ?_
  · simpa [unitVec] using l08tpo1_span_smul_singleton hs (unitVec t a)
  · exact (l08tpo1_span_smul_singleton hβ (e' + σ • unitVec t a)).trans
      (l08tpo1_span_smul_singleton hε (e' + σ • unitVec t a)).symm

theorem extLeaf_B2a_signed (hLS : LeafModelSigned) {kd : PlaneKind} (hkd : kd ≠ .orthogonal 0)
    {t : ℕ} (ht : 4 ≤ t) {vx z : V t} {ℓ j k : Code t} {U : Submodule F (V t)}
    (h : ExtShapeB2a vx ℓ U j z k) : InLLeafAt (planeEntry kd t) vx z ℓ k := by
  obtain ⟨b, e', μ, ε, σ, β, hμ, hε, hσ, hβ, he'b, he'i, hvx, hℓ, _hj, _hU, hz, hk⟩ := h
  subst hvx; subst hℓ; subst hz; subst hk
  have he : ∀ i, (ε • (e' + σ • unitVec t b)) i ≠ 0 :=
    extKey_ne_zero he'b he'i hε hσ
  have hmodel := hLS t ht (ε • (e' + σ • unitVec t b)) he b
  change LeafModelOn t (PlaneRaw.normalizerOf kd t (.extension (ε • (e' + σ • unitVec t b))))
    (PlaneRaw.normalizerOf kd t (.zero (Finset.univ.erase b)))
    (μ • (e' + σ • unitVec t b)) (β • unitVec t b)
  rw [normalizerOf_zero_erase_signed hkd ht b,
    normalizerOf_extension kd (ε • (e' + σ • unitVec t b))]
  refine hmodel.congr_span ?_ ?_
  · exact (l08tpo1_span_smul_singleton hμ (e' + σ • unitVec t b)).trans
      (l08tpo1_span_smul_singleton hε (e' + σ • unitVec t b)).symm
  · simpa [unitVec] using l08tpo1_span_smul_singleton hβ (unitVec t b)

theorem extLeaf_B2a_even (hLE : LeafModelEvenSigned) {t : ℕ} (ht : 4 ≤ t) {vx z : V t}
    {ℓ j k : Code t} {U : Submodule F (V t)} (h : ExtShapeB2a vx ℓ U j z k) :
    InLLeafAt (planeEntry (.orthogonal 0) t) vx z ℓ k := by
  obtain ⟨b, e', μ, ε, σ, β, hμ, hε, hσ, hβ, he'b, he'i, hvx, hℓ, _hj, _hU, hz, hk⟩ := h
  subst hvx; subst hℓ; subst hz; subst hk
  have he : ∀ i, (ε • (e' + σ • unitVec t b)) i ≠ 0 :=
    extKey_ne_zero he'b he'i hε hσ
  have hmodel := hLE t ht (ε • (e' + σ • unitVec t b)) he b
  change LeafModelOn t (PlaneRaw.normalizerOf (.orthogonal 0) t (.extension (ε • (e' + σ • unitVec t b))))
    (PlaneRaw.normalizerOf (.orthogonal 0) t (.zero (Finset.univ.erase b)))
    (μ • (e' + σ • unitVec t b)) (β • unitVec t b)
  rw [normalizerOf_zero_even (Finset.univ.erase b),
    normalizerOf_extension (.orthogonal 0) (ε • (e' + σ • unitVec t b))]
  refine hmodel.congr_span ?_ ?_
  · exact (l08tpo1_span_smul_singleton hμ (e' + σ • unitVec t b)).trans
      (l08tpo1_span_smul_singleton hε (e' + σ • unitVec t b)).symm
  · simpa [unitVec] using l08tpo1_span_smul_singleton hβ (unitVec t b)

theorem extLeaf_B2b (hLF : LeafModelFlip) (kd : PlaneKind) {t : ℕ} (ht : 4 ≤ t) {vx z : V t}
    {ℓ j k : Code t} {U : Submodule F (V t)} (h : ExtShapeB2b vx ℓ U j z k) :
    InLLeafAt (planeEntry kd t) vx z ℓ k := by
  obtain ⟨b, e', μ, ε, ε', σ, β, hμ, hε, hε', hσ, hβ, he'b, he'i, hvx, hℓ, _hj, _hU, hz,
    hk⟩ := h
  subst hvx; subst hℓ; subst hz; subst hk
  have he : ∀ i, (ε • (e' + σ • unitVec t b)) i ≠ 0 :=
    extKey_ne_zero he'b he'i hε hσ
  have hw' : ∀ i, (e' - σ • unitVec t b) i ≠ 0 := by
    intro i
    have h1 := extKey_sub_ne_zero (t := t) (b := b) (e' := e') he'b he'i
      (ε := (1 : F)) (σ := σ) one_ne_zero hσ i
    simpa using h1
  have hupd : Function.update (ε • (e' + σ • unitVec t b)) b
        (-(ε • (e' + σ • unitVec t b)) b) = ε • (e' - σ • unitVec t b) := by
    funext i
    by_cases hi : i = b
    · subst i
      have hub : (ε • (e' + σ • unitVec t b)) b = ε * σ := by
        simp [unitVec, he'b, smul_eq_mul]
      have hrb : (ε • (e' - σ • unitVec t b)) b = -(ε * σ) := by
        simp [unitVec, he'b, smul_eq_mul, mul_neg]
      rw [Function.update_self, hub, hrb]
    · rw [Function.update_apply, if_neg hi]
      simp [unitVec, Pi.single_apply, hi, smul_eq_mul]
  have hgroup : twistedPermGroupOn t (ε • (e' - σ • unitVec t b)) =
      twistedPermGroupOn t (ε' • (e' - σ • unitVec t b)) :=
    (twistedPermGroupOn_smul hw' hε).trans (twistedPermGroupOn_smul hw' hε').symm
  change LeafModelOn t (twistedPermGroupOn t (ε • (e' + σ • unitVec t b)))
    (twistedPermGroupOn t (ε' • (e' - σ • unitVec t b)))
    (μ • (e' + σ • unitVec t b)) (β • (e' - σ • unitVec t b))
  have hmodel := hLF t ht (ε • (e' + σ • unitVec t b)) he b
  rw [hupd] at hmodel
  rw [hgroup] at hmodel
  refine hmodel.congr_span ?_ ?_
  · exact (l08tpo1_span_smul_singleton hμ (e' + σ • unitVec t b)).trans
      (l08tpo1_span_smul_singleton hε (e' + σ • unitVec t b)).symm
  · exact (l08tpo1_span_smul_singleton hβ (e' - σ • unitVec t b)).trans
      (l08tpo1_span_smul_singleton hε (e' - σ • unitVec t b)).symm

end

end CFSG.StandardType.GGQ2Frame
