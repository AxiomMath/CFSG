module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstarOddHilb
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstarOddSiegel
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddEnd

public section

namespace CFSG.StandardType

namespace OrthBstarOdd

open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL Matrix

theorem mem_of_eq_mul_of_sq {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {φ ι c : G}
    (hι : ι ∈ N) (hφ : φ = ι * c) (hc : c * c = 1) {p : ℕ} (hp : Odd p) (hφp : φ ^ p = 1) :
    φ ∈ N := by
  have h1 : ((φ : G) : G ⧸ N) = (c : G ⧸ N) := by
    rw [hφ, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff ι).mpr hι, one_mul]
  have h2 : ((φ : G) : G ⧸ N) ^ p = 1 := by rw [← QuotientGroup.mk_pow, hφp, QuotientGroup.mk_one]
  have h3 : ((φ : G) : G ⧸ N) ^ 2 = 1 := by
    rw [h1, ← QuotientGroup.mk_pow, sq, hc, QuotientGroup.mk_one]
  have hcop : Nat.Coprime p 2 := Nat.Coprime.symm ((Nat.coprime_two_left).mpr hp)
  have h4 : orderOf ((φ : G) : G ⧸ N) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h4
  exact h4

variable {K : Type} [Field K]

theorem scalar_mulVec {d : ℕ} (a : Kˣ) (v : Fin d → K) :
    (Matrix.GeneralLinearGroup.scalar (Fin d) a : GL (Fin d) K).val *ᵥ v = (a : K) • v := by
  ext i
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem iterate_coordinateSemilinearMap {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (g : similarityPairs Q) (k : ℕ) (v : Fin d → K) :
    (⇑(coordinateSemilinearMap g.val))^[k] v = coordinateSemilinearMap (g ^ k).val v := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, pow_zero]
    exact (coordinateSemilinearMap_one v).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ', Subgroup.coe_mul,
      coordinateSemilinearMap_mul]

theorem conjAct_mulVec {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (g : similarityPairs Q)
    (X : matrixDerived Q) (w : Fin d → K) :
    ((conjAct Q g X : matrixDerived Q) : GL (Fin d) K).val *ᵥ coordinateSemilinearMap g.val w =
      coordinateSemilinearMap g.val (((X : GL (Fin d) K)).val *ᵥ w) := by
  rw [conjAct_apply, matrixDerivedConjugation_val]
  have hcf := coordinateFieldMap_matrix g.val.right (X : GL (Fin d) K) w
  change matrixLinearEquiv (g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K
      g.val.right (X : GL (Fin d) K) * g.val.left⁻¹)
      (matrixLinearEquiv g.val.left (coordinateFieldMap d g.val.right w)) =
    matrixLinearEquiv g.val.left (coordinateFieldMap d g.val.right
      (matrixLinearEquiv (X : GL (Fin d) K) w))
  rw [hcf, ← LinearEquiv.mul_apply, ← matrixLinearEquiv_mul, ← LinearEquiv.mul_apply,
    ← matrixLinearEquiv_mul, inv_mul_cancel_right]

variable [Finite K] [CharP K 2]

theorem exists_semi_of_aut {n : ℕ} (hn4 : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hpo : Odd p)
    {φ : MulAut (matrixDerived (Qm n hn4 b c))} (hφp : φ ^ p = 1)
    (hφI : φ ∉ OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c))) :
    ∃ (G : (Fin (2 * n) → K) ≃+ (Fin (2 * n) → K)) (σ : K ≃+* K) (μ a : K),
      (∀ (x : K) v, G (x • v) = σ x • G v) ∧ μ ≠ 0 ∧
      (∀ v, Qm n hn4 b c (G v) = μ * σ (Qm n hn4 b c v)) ∧ (∀ v, (⇑G)^[p] v = a • v) ∧
      σ ^ p = 1 ∧ σ ≠ 1 ∧
      ∀ (X : matrixDerived (Qm n hn4 b c)) (w : Fin (2 * n) → K),
        ((φ X : matrixDerived (Qm n hn4 b c)) : GL (Fin (2 * n)) K).val *ᵥ G w =
          G (((X : GL (Fin (2 * n)) K)).val *ᵥ w) := by
  have hn : 1 ≤ n := by omega
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus n K b c hn4 hirr
  have hQ : ∃ v, Qm n hn4 b c v ≠ 0 := exists_ne_zero_of_polar_nondegenerate (by omega) _ hnd
  have htop :=
    CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn4 b c hirr
  have hAP := coordinate_minus_point_action_properties n K b c hn4 hirr
  obtain ⟨g, rfl⟩ := exists_pair_of_aut hQ htop φ
  obtain ⟨mu, hmu⟩ := g.property
  have h1 : conjAct (Qm n hn4 b c) (g ^ p) = 1 := by rw [map_pow, hφp]
  have h2 : matrixProjectiveConjugationHom (Qm n hn4 b c) (g ^ p) = 1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective _ x
    change matrixProjectiveConjugation _ _ (matrixProjectiveProjection _ A) =
      matrixProjectiveProjection _ A
    rw [matrixProjectiveConjugation_mk]
    congr 1
    exact congrArg (fun α : MulAut (matrixDerived (Qm n hn4 b c)) => α A) h1
  obtain ⟨hright, a, ha⟩ :=
    (CFSG.RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _ hnd hT hAP
      _).1 h2
  have hrp : (g ^ p).val.right = g.val.right ^ p := by
    change (g.val ^ p).right = _
    exact map_pow SemidirectProduct.rightHom _ p
  refine ⟨coordinateSemilinearMap g.val, g.val.right, (mu : K), (a : K),
    fun x v => coordinateSemilinearMap_smul g.val x v, Units.ne_zero mu, hmu, fun v => ?_,
    by rw [← hrp, hright], fun hσ => ?_, fun X w => conjAct_mulVec g X w⟩
  · rw [iterate_coordinateSemilinearMap, coordinateSemilinearMap_apply, ha, hright]
    exact scalar_mulVec a v
  ·
    obtain ⟨B, hB⟩ := CFSG.RankThree.PartOne.OutStructure.exists_isometry_of_linear _ hQ
      ⟨g, (mem_linearSimilarityPairs_iff _ _).2 hσ⟩
    have hgB := conjAct_eq_of_isometry hB
    obtain ⟨w, hw⟩ := hQ
    rcases mem_or_mul_reflMat_mem hnd hT B.2 w hw with hBΓ | hBΓ
    · exact hφI (hgB ▸ conjAct_inclusion_mem_inner B hBΓ)
    · have hR := reflMat_mem_isometries (Q := Qm n hn4 b c) w hw
      have hιB : matrixIsometryInclusion (Qm n hn4 b c) B =
          matrixIsometryInclusion (Qm n hn4 b c)
            ⟨B.val * reflMat (Qm n hn4 b c) w hw, mul_mem B.2 hR⟩ *
            matrixIsometryInclusion (Qm n hn4 b c) ⟨reflMat _ w hw, hR⟩ := by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        change B.val = B.val * reflMat _ w hw * reflMat _ w hw
        rw [mul_assoc, reflMat_mul_self, mul_one]
      apply hφI
      refine mem_of_eq_mul_of_sq (conjAct_inclusion_mem_inner
        ⟨B.val * reflMat (Qm n hn4 b c) w hw, mul_mem B.2 hR⟩ hBΓ) ?_
        (reflAut_mul_self (Q := Qm n hn4 b c) w hw) hpo hφp
      rw [hgB, hιB, map_mul]
      rfl

end OrthBstarOdd

end CFSG.StandardType
