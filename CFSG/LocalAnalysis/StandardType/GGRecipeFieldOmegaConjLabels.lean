module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaConj
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly QuadraticMap CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL

namespace RecipeFieldOmega

section Recipe

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem pow_mem_inner_of_mul_pow_eq_one {G : Type*} [Group G] {u f : MulAut G}
    (hu : u ∈ inner G) {p : ℕ} (h : (u * f) ^ p = 1) : f ^ p ∈ inner G := by
  obtain ⟨d, hd, hdp⟩ := exists_mul_pow_eq (hD := inner_normal G) (inner G) hu (f := f) p
  rw [h] at hdp
  rw [eq_inv_of_mul_eq_one_right hdp.symm]
  exact inv_mem hd

theorem conj_conclusion_of_congr {R Γ : Type*} [Group R] [Group Γ] (Θ : R ≃* Γ)
    {F : Set (MulAut R)} {u f f' : MulAut R} {γ : Γ} {g u' : MulAut Γ} {p : ℕ} (hp : p.Prime)
    (hf'F : f' ∈ F) (hγ : MulAut.conj γ = MulAut.congr Θ u) (hf : MulAut.congr Θ f = g)
    (hf' : MulAut.congr Θ f' = g) (hu' : u' ∈ inner Γ) (heq : MulAut.conj γ * g = u' * g * u'⁻¹)
    (hgp : g ^ p = 1) (hg1 : g ≠ 1) :
    ∃ f'' ∈ F, ∃ u'' ∈ LargeEvenInnSet R, orderOf f'' = p ∧ u * f = u'' * f'' * u''⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨f', hf'F, (MulAut.congr Θ).symm u',
    (mem_innSet_iff_congr Θ _).2 (by rw [MulEquiv.apply_symm_apply]; exact hu'), ?_, ?_⟩
  · refine orderOf_eq_prime ((MulAut.congr Θ).injective (by rw [map_pow, hf', hgp, map_one]))
      fun h1 => hg1 ?_
    rw [← hf', h1, map_one]
  · apply (MulAut.congr Θ).injective
    rw [map_mul, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hf, hf', ← hγ, heq]

theorem ggRawFieldConj_omegaPlus {m : ℕ} (hm3 : 3 ≤ m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGRawFieldConj p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) := by
  intro _ _ u hu f hf huf hord
  have hm : 1 ≤ m := by omega
  set Θ := plusEquiv (K := K) hm
  obtain ⟨σ, hσ⟩ := congr_plusEquiv_of_mem_closure hm hf
  obtain ⟨γ, hγ⟩ := (mem_innSet_iff_congr Θ u).1 hu
  have hcongr : MulAut.congr Θ (u * f) = MulAut.conj γ * AutOm.fieldAutP m σ := by
    rw [map_mul, ← hγ, hσ]
  obtain ⟨hnd, hT3⟩ := regular_coordinateQuadPlus m K hm3
  have hAP := coordinate_plus_point_action_properties m K hm3
  set S := CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair (coordinateQuadPlus m K) σ
    (CFSG.SeitzReduction.E7Pilot.coordinateQuadPlus_fieldMap m σ)
  have hfS : AutOm.fieldAutP m σ = conjAct _ S := AutOm.fieldAutP_apply m σ
  have hSmap : ∀ v, coordinateSemilinearMap S.val v = coordinateFieldMap (2 * m) σ v := fun v => by
    funext i
    simp [S, CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair, coordinateSemilinearMap_apply,
      coordinateFieldMap_apply]
  have hS : IsIsoPair (coordinateQuadPlus m K) S.val := fun v => by
    rw [hSmap]
    exact CFSG.SeitzReduction.E7Pilot.coordinateQuadPlus_fieldMap m σ v
  have hSw : coordinateSemilinearMap S.val (CFSG.SeitzReduction.OmegaPilot.plusUnitVector hm) =
      CFSG.SeitzReduction.OmegaPilot.plusUnitVector hm := by
    rw [hSmap]
    exact CFSG.SeitzReduction.OmegaPilot.coordinateFieldMap_plusUnitVector hm σ
  have hout : MulAut.conj γ * conjAct _ S ∉ inner (matrixDerived (coordinateQuadPlus m K)) := by
    rw [← hfS, ← hcongr, ← mem_innSet_iff_congr]
    exact huf
  have hord' : (MulAut.conj γ * conjAct _ S) ^ p = 1 := by
    rw [← hfS, ← hcongr, ← map_pow, hord, map_one]
  have hfp : conjAct _ S ^ p = 1 := by
    have h1 := pow_mem_inner_of_mul_pow_eq_one ⟨γ, rfl⟩ hord'
    rw [← hfS, ← map_pow] at h1
    rw [← hfS, ← map_pow, AutOm.eq_one_of_mem_inner_plusCompl hm3 (Or.inl rfl) h1, map_one]
  obtain ⟨u', hu', heq⟩ := exists_conj_of_isIsoPair hm hnd hT3 hAP hp hp2 hS
    (AutOm.plusUnitVector_form_ne_zero hm) hSw γ hout hord' hfp
  obtain ⟨φ, hφF, hφ⟩ := exists_mem_field_congr_plusEquiv hm σ
  refine conj_conclusion_of_congr Θ hp hφF hγ (hσ.trans hfS) (hφ.trans hfS) hu' heq hfp ?_
  intro h1
  apply hout
  rw [h1, mul_one]
  exact ⟨γ, rfl⟩

theorem isIsoPair_frobPair {n : ℕ} (hn : 1 ≤ n) {b c : K} (hb : b ≠ 0) :
    IsIsoPair (coordinateQuadMinus n K hn b c)
      ((frobPair n hn b c hb : similarityPairs (coordinateQuadMinus n K hn b c)) :
        coordinateSemilinearGroup (2 * n) K) := fun v => by
  change coordinateQuadMinus n K hn b c (coordinateSemilinearMap (frobElt n hn b c hb) v) =
    (frobeniusEquiv K 2) (coordinateQuadMinus n K hn b c v)
  rw [frobElt_apply, form_tailLin_sq, frobeniusEquiv_apply, frobenius_def]

theorem frobPair_pow_tailVec {n : ℕ} (hn : 1 ≤ n) {b c : K} (hb : b ≠ 0) (k : ℕ) :
    coordinateSemilinearMap ((frobPair n hn b c hb ^ k :
      similarityPairs (coordinateQuadMinus n K hn b c)) : coordinateSemilinearGroup (2 * n) K)
      (AutOm.tailVec n hn) = AutOm.tailVec n hn := by
  funext i
  rw [frobPair_pow_apply]
  by_cases h0 : i = tailZero n hn
  · subst h0
    simp [tailOne_ne_tailZero n hn]
  · by_cases h1 : i = tailOne n hn
    · subst h1
      simp [tailOne_ne_tailZero n hn]
    · simp [h0, h1]

theorem ggRawFieldConj_omegaMinus {n : ℕ} (hn4 : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f₀ : ℕ} (hf : Nat.card K = 2 ^ f₀) (hf1 : 1 ≤ f₀)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGRawFieldConj p (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))
      (LargeEvenInnSet _)
      (LargeEvenPhiQ (n - 1) b c
        (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))) := by
  intro _ _ u hu f hfcl huf hord
  have hn : 1 ≤ n := by omega
  have hb := ne_zero_of_irreducible_tail b c hirr
  set Θ := minusEquiv (K := K) hn4 b c
  set τ := AutOm.frobAut hn4 hirr
  obtain ⟨k, hk⟩ : ∃ k : ℕ, MulAut.congr Θ f = τ ^ k := by
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1
      ((AutOm.isOfFinOrder_frobAut hn4 hirr hf hf1).mem_powers_iff_mem_zpowers.2
        (congr_minusEquiv_of_mem_closure hn4 hirr hfcl))
    exact ⟨k, hk.symm⟩
  obtain ⟨γ, hγ⟩ := (mem_innSet_iff_congr Θ u).1 hu
  have hcongr : MulAut.congr Θ (u * f) = MulAut.conj γ * τ ^ k := by rw [map_mul, ← hγ, hk]
  obtain ⟨hnd, hT3⟩ := regular_coordinateQuadMinus n K b c hn4 hirr
  have hAP := coordinate_minus_point_action_properties n K b c hn4 hirr
  set S := (frobPair n hn b c hb) ^ k
  have hτS : τ ^ k = conjAct (Qm n hn4 b c) S := by
    change τ ^ k = conjAct (Qm n hn4 b c) (frobPair n hn b c hb ^ k)
    rw [map_pow]
    rfl
  have hS : IsIsoPair (Qm n hn4 b c) S.val := by
    rw [SubmonoidClass.coe_pow]
    exact (isIsoPair_frobPair hn hb).pow k
  have hout : MulAut.conj γ * conjAct _ S ∉
      ComponentClassification.OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)) := by
    rw [← hτS, ← hcongr, ← mem_innSet_iff_congr]
    exact huf
  have hord' : (MulAut.conj γ * conjAct _ S) ^ p = 1 := by
    rw [← hτS, ← hcongr, ← map_pow, hord, map_one]
  have hfp : conjAct _ S ^ p = 1 := by
    have h1 := pow_mem_inner_of_mul_pow_eq_one ⟨γ, rfl⟩ hord'
    rw [← hτS, ← pow_mul] at h1
    have h2 : τ ^ (k * p) ∈ ComponentClassification.OuterAutomorphisms.inner
        (matrixDerived (Qm n hn4 b c)) ⊓ Subgroup.zpowers τ :=
      ⟨h1, Subgroup.npow_mem_zpowers _ _⟩
    rw [AutOm.inner_inf_zpowers_frobAut hn4 hirr hf hf1, Subgroup.mem_bot] at h2
    rw [← hτS, ← pow_mul, h2]
  obtain ⟨u', hu', heq⟩ := exists_conj_of_isIsoPair hn hnd hT3 hAP hp hp2 hS
    (AutOm.tailVec_form_ne_zero n hn b c) (frobPair_pow_tailVec hn hb k) γ hout hord' hfp
  obtain ⟨φ, hφF, hφ⟩ := exists_mem_phi_congr_minusEquiv hn4 hirr k
  refine conj_conclusion_of_congr Θ hp hφF hγ (hk.trans hτS) (hφ.trans hτS) hu' heq hfp ?_
  intro h1
  apply hout
  rw [h1, mul_one]
  exact ⟨γ, rfl⟩

end Recipe

end RecipeFieldOmega

open RecipeFieldOmega

theorem ggRawFieldConjOn_omegaPlus : GGRawFieldConjOn fun _ lab => GGOmegaPlusLabel lab :=
  fun _ hp hp2 _ _ ⟨ht, h4⟩ => largeEvenLabelAll_omegaPlus ht h4 fun _ _ _ _ _ =>
    ggRawFieldConj_omegaPlus (by omega) hp hp2

theorem ggRawFieldConjOn_omegaMinus : GGRawFieldConjOn fun _ lab => GGOmegaMinusLabel lab :=
  fun _ hp hp2 _ hlab ⟨ht, h4⟩ => largeEvenLabelAll_omegaMinus ht h4 fun _ _ _ _ hK _ _ hirr =>
    ggRawFieldConj_omegaMinus h4 hirr hK hlab.1 hp hp2

end CFSG.StandardType
