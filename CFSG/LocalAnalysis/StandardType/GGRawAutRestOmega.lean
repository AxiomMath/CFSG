module

public import CFSG.LocalAnalysis.StandardType.GGRawAutRestCore
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmega
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  RecipeFieldOmega

namespace RawAutOmega

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem ggOddAutInnField_omegaPlus_of {m : ℕ} (hm : 1 ≤ m) {p M : ℕ} (hpM : Nat.Coprime M p)
    (hdec : ∀ α : MulAut (matrixDerived (coordinateQuadPlus m K)),
      ∃ ι ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
          (matrixDerived (coordinateQuadPlus m K)),
        ∃ (y : MulAut (matrixDerived (coordinateQuadPlus m K))) (σ : K ≃+* K),
          y * AutOm.fieldAutP m σ = AutOm.fieldAutP m σ * y ∧ y ^ M = 1 ∧
            α = ι * y * AutOm.fieldAutP m σ) :
    GGOddAutInnField p (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) := by
  intro φ hφ
  set Θ := plusEquiv (K := K) hm
  have hS : MulAut.congr Θ φ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner _ ⊔ (AutOm.fieldAutP m).range := by
    obtain ⟨ι, hι, y, σ, hyσ, hyM, hα⟩ := hdec (MulAut.congr Θ φ)
    refine RecipeFieldOmega.mem_of_pow_mem_of_coprime _ (a := M) (N := p) ?_
      (by rw [← map_pow, hφ, map_one]) hpM
    obtain ⟨ι', hι', h⟩ := RecipeFieldOmega.exists_pow_eq_mul_pow
      (CFSG.ComponentClassification.OuterAutomorphisms.inner _) hι hyσ M
    rw [hα, h, hyM, mul_one, ← map_pow]
    exact Subgroup.mul_mem_sup hι' ⟨_, rfl⟩
  obtain ⟨ι, hι, _, ⟨σ, rfl⟩, hs⟩ := Subgroup.mem_sup_of_normal_left.1 hS
  obtain ⟨ψ, hψ, hψσ⟩ := exists_mem_field_congr_plusEquiv hm σ
  refine ⟨(MulAut.congr Θ).symm ι, (RecipeFieldOmega.mem_innSet_iff_congr Θ _).2 (by
    rwa [MulEquiv.apply_symm_apply]), ψ, Subgroup.subset_closure hψ, ?_⟩
  apply (MulAut.congr Θ).injective
  rw [map_mul, MulEquiv.apply_symm_apply, hψσ, hs]

theorem ggOddAutInnField_omegaPlus {m : ℕ} (hm5 : 5 ≤ m) {p : ℕ} (hp : Odd p) :
    GGOddAutInnField p (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) := by
  have hm : 1 ≤ m := by omega
  refine ggOddAutInnField_omegaPlus_of hm (M := 2) (Nat.coprime_two_left.2 hp) fun α => ?_
  obtain ⟨ι, hι, c, hc, hα⟩ := AutOm.exists_inner_mul_plusCompl hm5 α
  obtain ⟨y, hy, σ, rfl⟩ := exists_eq_mul_fieldAutP_of_mem_plusCompl hm hc
  refine ⟨ι, hι, y, σ, ?_, ?_, by rw [hα, mul_assoc]⟩
  · rcases hy with rfl | rfl
    · rw [one_mul, mul_one]
    · exact AutOm.plusRefl_mul_fieldAutP hm σ
  · rcases hy with rfl | rfl
    · exact one_pow 2
    · rw [sq]
      exact AutOm.plusRefl_mul_self hm

theorem exists_eq_mul_mul_fieldAutP_four
    (α : MulAut (matrixDerived (coordinateQuadPlus 4 K))) :
    ∃ ι ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixDerived (coordinateQuadPlus 4 K)),
      ∃ (y : MulAut (matrixDerived (coordinateQuadPlus 4 K))) (σ : K ≃+* K),
        y * AutOm.fieldAutP 4 σ = AutOm.fieldAutP 4 σ * y ∧ y ^ 6 = 1 ∧
          α = ι * y * AutOm.fieldAutP 4 σ := by
  have h14 : 1 ≤ 4 := by norm_num
  obtain ⟨θ, h3, hρθ, hφθ, hgen, -, -⟩ := plusFourTrialityInput_holds K
  obtain ⟨ι, hι, k, c, hc, hα⟩ := hgen α
  obtain ⟨y, hy, σ, rfl⟩ := exists_eq_mul_fieldAutP_of_mem_plusCompl h14 hc
  have hyc : y * AutOm.fieldAutP 4 σ = AutOm.fieldAutP 4 σ * y := by
    rcases hy with rfl | rfl
    · rw [one_mul, mul_one]
    · exact AutOm.plusRefl_mul_fieldAutP h14 σ
  refine ⟨ι, hι, θ ^ k * y, σ, ?_, ?_, by rw [hα]; simp only [mul_assoc]⟩
  · rw [mul_assoc, hyc, ← mul_assoc, ← AutOm.fieldAutP_mul_pow hφθ σ k, mul_assoc]
  · rcases hy with rfl | rfl
    · rw [mul_one, ← pow_mul, show k * 6 = 3 * (2 * k) by ring, pow_mul, h3, one_pow]
    · have h2 : (θ ^ k * AutOm.plusRefl h14) ^ 2 = 1 := by
        rw [sq, mul_assoc, ← mul_assoc (AutOm.plusRefl h14),
          AutOm.plusRefl_mul_pow le_rfl h3 hρθ k, mul_assoc, AutOm.plusRefl_mul_self,
          mul_one, ← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, h3, one_pow]
      rw [show 6 = 2 * 3 by norm_num, pow_mul, h2, one_pow]

theorem ggOddAutInnField_omegaPlusFour {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    GGOddAutInnField p (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))) := by
  have hcop : Nat.Coprime 6 p := by
    rw [show 6 = 2 * 3 by norm_num, Nat.coprime_mul_iff_left]
    exact ⟨(Nat.coprime_primes Nat.prime_two hp).2 hp2.symm,
      (Nat.coprime_primes Nat.prime_three hp).2 hp3.symm⟩
  exact ggOddAutInnField_omegaPlus_of (by norm_num) hcop exists_eq_mul_mul_fieldAutP_four

theorem exists_inner_mul_field_omegaMinus {n : ℕ} (hn4 : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (φ : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))) :
    ∃ u ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (n - 1) b c))),
      ∃ g ∈ Subgroup.closure (LargeEvenPhiQ (n - 1) b c
          (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))), φ = u * g := by
  set Θ := minusEquiv (K := K) hn4 b c
  obtain ⟨ι, hι, k, hk⟩ := AutOm.exists_inner_mul_frobAut_pow hn4 hirr hf (MulAut.congr Θ φ)
  obtain ⟨ψ, hψ, hψk⟩ := exists_mem_phi_congr_minusEquiv hn4 hirr k
  refine ⟨(MulAut.congr Θ).symm ι, (RecipeFieldOmega.mem_innSet_iff_congr Θ _).2 (by
    rwa [MulEquiv.apply_symm_apply]), ψ, Subgroup.subset_closure hψ, ?_⟩
  apply (MulAut.congr Θ).injective
  rw [map_mul, MulEquiv.apply_symm_apply, hψk, ← hk]

end RawAutOmega

open RawAutOmega

theorem ggOddAutOn_omegaPlus : GGOddAutOn GGOmegaPlusLabel := by
  intro p lab hp hp2 _ hS hD4
  obtain ⟨ht, h4⟩ := hS
  show LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    GGOddAutInnField p I F
  refine largeEvenLabelAll_omegaPlus ht h4 fun K _ _ _ _ _ _ => ?_
  rcases Nat.lt_or_ge lab.rank 5 with h5 | h5
  · have hr : lab.rank = 4 := by omega
    rw [hr]
    exact ggOddAutInnField_omegaPlusFour hp hp2 fun h3 => hD4 ⟨ht, hr, h3⟩
  · exact ggOddAutInnField_omegaPlus h5 (hp.odd_of_ne_two hp2)

theorem ggOddAutOn_omegaMinus : GGOddAutOn GGOmegaMinusLabel := by
  intro p lab _ _ hlab hS _
  obtain ⟨ht, h4⟩ := hS
  show LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    GGOddAutInnField p I F
  exact largeEvenLabelAll_omegaMinus ht h4 fun _ _ _ _ hK _ _ hirr _ _ =>
    RawAut.ggOddAutInnField_of_forall (exists_inner_mul_field_omegaMinus h4 hirr hK)

end CFSG.StandardType

end
