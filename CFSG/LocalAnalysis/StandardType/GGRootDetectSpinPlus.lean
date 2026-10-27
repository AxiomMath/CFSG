module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectSpin
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutSim
public import CFSG.LieType.Steinberg.Classical.SpinPlus.Unipotent
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
public import CFSG.RankThree.PartOne.S11d.LieCentralizerOrth
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthOmega
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel
public import CFSG.LieType.Universal.SpinClause0
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsDomain
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofTypeAC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalConj
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSplit
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.LieType.Steinberg.SpinFrame
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open scoped Matrix Pointwise

@[expose] def RootDetectAt (U : LieUniversal) (q : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (ψ : U.K →* G), ψ.ker ≤ Subgroup.center U.K →
    ∀ p : ℕ, p.Prime → p ≠ 2 → q p →
    ∀ c ∈ Subgroup.normalizer (ψ.range : Set G),
      c ^ p ∈ Subgroup.centralizer (ψ.range : Set G) →
      ∀ γ ∈ U.D.roots, ∀ u : U.K, GGTorusOnRoot U.D ψ c γ u → GGPsiInnerDiag U.D ψ c

section Assemble

theorem ggRootDetect_of_rootDetectAt {t : StatedLieTag}
    (h : ∀ n f, StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
      RootDetectAt (ggU t n f) fun p => ¬(t = .POmegaPlus ∧ n = 4 ∧ p = 3)) :
    GGRootDetect t := by
  intro G _ _ n f ψ hadm hrk hker p hp hp2 hD c hc hcp γ hγ u hT
  exact h n f hadm hrk G ψ hker p hp hp2 hD c hc hcp γ hγ u hT

end Assemble

namespace RootDetectSpin

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem mul_self_mem_statedOmega [Finite K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}
    (hQ : ⇑Q = Q₀) (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (B : GL ι K) (hB : ∀ v, Q ((B : Matrix ι ι K) *ᵥ v) = Q v) : B * B ∈ StatedOmega Q₀ := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ, Subgroup.mem_comap, map_mul]
  have hO : (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom B ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    change Q (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K B v) = Q v
    rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
    exact hB v
  obtain ⟨-, -, -, -, -, hsq, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hnd hT
  have h := hsq _ hO
  rwa [pow_two] at h

theorem eq_one_of_mk_eq_one [CharP K 2] [Nonempty ι] {Q : QuadraticForm K (ι → K)}
    {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (x : StatedOmega Q₀) (hx : (x : StatedProj (StatedOmega Q₀)) = 1) : x = 1 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
  have hs := (CFSG.ClassicalGroups.Orthogonal.mem_statedScalars_iff (x : GL ι K)).mp hx
  have hΩ : CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K x ∈
      CFSG.RankThree.Classical2.orthDerived Q := by
    exact Subgroup.mem_comap.mp ((CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ).le x.2)
  have h1 := CFSG.RankThree.PartOne.eq_one_of_mem_scalars_of_mem_orthDerived hnd hΩ hs
  apply Subtype.ext
  exact (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).injective (by
    rw [h1, Subgroup.coe_one, map_one])

theorem longRoot_hroot {Q : QuadraticForm K (ι → K)} {n : ℕ} {F : HypFrame Q n}
    {idx : Fin n → Bool → ι} (hF : IsCoordFrame F idx) {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    (∀ c : K, ((spinMatrix Q (F.longRoot hij s t (.ofAdd c)) : GL ι K) : Matrix ι ι K) =
      1 + c • longMat K idx i j s t) ∧ longMat K idx i j s t ≠ 0 ∧
      ∀ φ : K ≃+* K, (longMat K idx i j s t).map φ = longMat K idx i j s t := by
  refine ⟨fun c => coe_spinMatrix_longRoot hF hij s t c, ?_, fun φ => ?_⟩
  · intro h0
    have h1 := congrFun (congrFun h0 (idx i s)) (idx j (!t))
    have hne : idx j t ≠ idx i s := idx_ne hF hij.symm t s
    simp [longMat, hne] at h1
  · simp only [longMat, Matrix.map_sub _ (map_sub φ), Matrix.map_single, map_one]

theorem exists_similarity_plus_four_of_pow {F : Type} [Field F] [Finite F] {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (β : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 F)))) (hβ : β ^ p = 1) :
    ∃ (A : GL (Fin 4 ⊕ Fin 4) F) (φ : F ≃+* F) (μ : Fˣ),
      (∀ v, quadPlus 4 F (A.val *ᵥ (fun i => φ (v i))) = μ * φ (quadPlus 4 F v)) ∧
      ∀ x : StatedOmega (StatedQuadPlus 4 F), ∃ y : StatedOmega (StatedQuadPlus 4 F),
        (y : GL (Fin 4 ⊕ Fin 4) F) = A * glFieldEquiv _ φ (x : GL _ F) * A⁻¹ ∧
          β (QuotientGroup.mk x) = QuotientGroup.mk y := by
  have h : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 F))) .POmegaPlus 4 2 f :=
    ⟨⟨Nat.prime_two, hf, le_rfl⟩, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
  have hEA := (orthogonal_geometry_plus_model_stabilizer_preserving_image h F hF
    (MulEquiv.refl _)).1
  have horbit :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit.orthogonal_geometry_plus_point_family_orbit
      h hF (MulEquiv.refl _)
  have hidx : (matrixProjectiveImage (coordinateQuadPlus 4 F)).index ≤ 3 := by
    have hst : (projectivePointFamilyAut (coordinateQuadPlus 4 F)).index =
        (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)))
          (projectivePointFamily (coordinateQuadPlus 4 F))).ncard :=
      MulAction.index_stabilizer _ _
    rw [← hEA, hst]
    exact (horbit.2.2.2.2.2 rfl).2
  have hpow : (MulAut.congr (CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance.statedProjectiveReindexEquiv
      (plusIndexEquiv 4) (quadPlus 4 F) (coe_quadPlus 4 F)) β) ^ p = 1 := by
    rw [← map_pow, hβ, map_one]
  refine CFSG.ClassicalInvolution.ModelFacts.OrthAut.exists_similarity_of_mem_image
    (plusIndexEquiv 4) (quadPlus 4 F) (coe_quadPlus 4 F) β ?_
  have hidx' : (matrixProjectiveImage
      (reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 F))).index ≤ 3 := hidx
  exact CFSG.RankThree.PartOne.OutStructure.mem_of_pow_mem_of_index_le_three _ hidx' hp hp3
    (k := 1) (by rw [pow_one, hpow]; exact one_mem _)

theorem rootDetectAt_spinPlus {F : Type} [Field F] [Finite F] [CharP F 2] {n f : ℕ}
    (hn : 4 ≤ n) (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f) {q : ℕ → Prop}
    (hq : ∀ p, p.Prime → p ≠ 2 → q p → n = 4 → 3 < p) :
    RootDetectAt ⟨spinGroup (quadPlus n F), plusDatum n F (by omega)⟩ q := by
  intro G _ _ ψ hker p hp hp2 hqp c hc hcp γ hγ u hT
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    Finite.of_injective _ ((MonoidHom.ker_eq_bot_iff _).mp
      (ker_spinMatrix_quadPlus_eq_bot (K := F) (n := n) CharTwo.two_eq_zero))
  have : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨hsurj, -, hZ⟩ := spinToStatedProj_quadPlus (K := F) hn3
  have hnd := nondegenerate_polarBilin_quadPlus n F
  have hT3 := CFSG.ComponentClassification.RankTwoClassical.exists_totallySingular_quadPlus hn3 F
  have hform : ∀ β : MulAut (StatedProj (StatedOmega (StatedQuadPlus n F))), β ^ p = 1 →
      ∃ (A : GL (Fin n ⊕ Fin n) F) (φ : F ≃+* F) (μ : Fˣ),
        (∀ v, quadPlus n F (A.val *ᵥ (fun i => φ (v i))) = μ * φ (quadPlus n F v)) ∧
        ∀ x : StatedOmega (StatedQuadPlus n F), ∃ y : StatedOmega (StatedQuadPlus n F),
          (y : GL (Fin n ⊕ Fin n) F) = A * glFieldEquiv _ φ (x : GL _ F) * A⁻¹ ∧
            β (QuotientGroup.mk x) = QuotientGroup.mk y := by
    intro β hβ
    rcases Nat.lt_or_ge n 5 with h4 | h5
    · obtain rfl : n = 4 := by omega
      exact exists_similarity_plus_four_of_pow hf hF hp (hq p hp hp2 hqp rfl) β hβ
    · exact CFSG.ClassicalInvolution.ModelFacts.OrthAut.exists_similarity_plus
        ⟨Nat.prime_two, hf, hn⟩ h5 hF β
  obtain ⟨i, j, hij, s, t, -, hXγ⟩ := exists_plusRootGroup_eq (K := F) hn3 hγ
  obtain ⟨hmat, hE0, hEφ⟩ := RootDetectSpin.longRoot_hroot
    (CFSG.LieType.Steinberg.SpinPlus.isCoordFrame_plusFrame (K := F) hn3) hij s t
  refine RootDetectSpin.ggPsiInnerDiag_spin_of_aut (range_spinMatrix_quadPlus hn3)
    (isPerfect_spinGroup_quadPlus (K := F) hn3).commutator_eq_top hsurj hZ
    (RootDetectSpin.mul_self_mem_statedOmega (coe_quadPlus n F) hnd hT3)
    (RootDetectSpin.eq_one_of_mk_eq_one (coe_quadPlus n F) hnd) (hp.odd_of_ne_two hp2) hform
    (plusDatum n F hn3) (RootDetectSpin.detect_of_linear (x := fun c =>
      (plusFrame n F hn3).longRoot hij s t (.ofAdd c)) (fun c => ?_) hmat hE0 hEφ) hker hc hcp hT
  change _ ∈ plusRootGroup n F hn3 γ
  rw [hXγ]
  exact ⟨_, rfl⟩

end RootDetectSpin

section Family

theorem ggU_pOmegaPlus {n f : ℕ} (hn : 3 ≤ n) :
    ggU .POmegaPlus n f = ⟨spinGroup (quadPlus n (GaloisField 2 f)),
      plusDatum n (GaloisField 2 f) hn⟩ := by
  simp only [ggU, lieUniversal, hn, ↓reduceDIte]

theorem ggRootDetect_pOmegaPlus : GGRootDetect .POmegaPlus := by
  refine ggRootDetect_of_rootDetectAt fun n f hadm _ => ?_
  obtain ⟨-, hf, hn⟩ := hadm
  rw [ggU_pOmegaPlus (by omega)]
  refine RootDetectSpin.rootDetectAt_spinPlus hn hf (GaloisField.card 2 f (by omega))
    fun p hp hp2 hq hn4 => ?_
  have h3 : p ≠ 3 := fun h3 => hq ⟨rfl, hn4, h3⟩
  have := hp.two_le
  omega

end Family

end CFSG.StandardType
