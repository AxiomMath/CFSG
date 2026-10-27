module

public import CFSG.GroupTheory.OddKernelImage
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import CFSG.GroupTheory.SubgroupOfLattice
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Complements
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.GroupTheory.SteinbergBSQuotientLifting
public import CFSG.LocalAnalysis.StandardType.GGOTwoPrimeMap
public import CFSG.GH74.L5U5.ModelsPairsUnitary
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.PointKernelRootProductBasic
public import CFSG.RankThree.PartOne.KF.U4Model
public import CFSG.Assembly.OrderReductions.CharacterInflation
public import CFSG.GH74.Statements
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvolutionCountAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSetDoubleTransitivity
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimePairTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorOddKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientRoot
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureInvertedHullData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperCommutingImagesQuotient
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityPointTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.StrongEmbeddingRecognition
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate43
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section
namespace CFSG.StandardType

theorem ggOTwoPrime_commutation_of_map_of_central_odd_kernel
    {U V : Type*} [Group U] [Finite U] [Group V]
    (π : U →* V) (hπ : π.ker ≤ Subgroup.center U)
    (hodd : Odd (Nat.card π.ker)) (C D : Subgroup U)
    (hcomm : ∀ x ∈ (ggOTwoPrime C).map π,
      ∀ y ∈ (ggOTwoPrime D).map π, x * y = y * x) :
    ∀ x ∈ ggOTwoPrime C, ∀ y ∈ ggOTwoPrime D, x * y = y * x := by
  have hle : ggOTwoPrime C ≤ Subgroup.centralizer (ggOTwoPrime D : Set U) := by
    rw [ggOTwoPrime, Subgroup.closure_le]
    rintro x ⟨hx, k, hx2⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    have hxr : x ∈ ggOTwoPrime C := Subgroup.subset_closure ⟨hx, k, hx2⟩
    have hbar : π x * π y = π y * π x :=
      hcomm _ (Subgroup.mem_map.mpr ⟨x, hxr, rfl⟩)
        _ (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
    have hconj : (y * x * y⁻¹) ^ 2 ^ k = 1 := by
      change ((MulAut.conj y) x) ^ 2 ^ k = 1
      rw [← map_pow, hx2, map_one]
    have hker : x⁻¹ * (y * x * y⁻¹) ∈ π.ker := by
      change π (x⁻¹ * (y * x * y⁻¹)) = 1
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, ← hbar,
        mul_inv_cancel_right, inv_mul_cancel]
    have heq : x = y * x * y⁻¹ :=
      CFSG.ProperTwoGeneratedCore.RankOnePair.eq_of_inv_mul_mem_of_central_odd
        hπ hodd hx2 hconj hker
    calc
      y * x = (y * x * y⁻¹) * y := by group
      _ = x * y := by rw [← heq]
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm

theorem ggOTwoPrime_le_of_map_le_map_of_central_odd_kernel
    {U V : Type*} [Group U] [Finite U] [Group V]
    (π : U →* V) (hπ : π.ker ≤ Subgroup.center U)
    (hodd : Odd (Nat.card π.ker)) (C D : Subgroup U)
    (hmap : (ggOTwoPrime C).map π ≤ D.map π) : ggOTwoPrime C ≤ D := by
  rw [ggOTwoPrime, Subgroup.closure_le]
  rintro x ⟨hxC, k, hxpow⟩
  have hP : IsPGroup 2 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card_dvd_pow (n := k)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hxpow
  have hxres : x ∈ ggOTwoPrime C := Subgroup.subset_closure ⟨hxC, k, hxpow⟩
  have hle : (Subgroup.zpowers x).map π ≤ D.map π := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le_of_mem (hmap (Subgroup.mem_map.mpr ⟨x, hxres, rfl⟩))
  exact (CFSG.GroupTheory.le_of_map_le_map_of_odd hπ hodd hP hle)
    (Subgroup.mem_zpowers x)

theorem ggOTwoPrime_eq_of_map_eq_of_central_odd_kernel
    {U V : Type*} [Group U] [Finite U] [Group V]
    (π : U →* V) (hπ : π.ker ≤ Subgroup.center U)
    (hodd : Odd (Nat.card π.ker)) (C D : Subgroup U)
    (hD : ggOTwoPrime D = D)
    (hmap : (ggOTwoPrime C).map π = D.map π) : ggOTwoPrime C = D := by
  apply le_antisymm
  · exact ggOTwoPrime_le_of_map_le_map_of_central_odd_kernel π hπ hodd C D hmap.le
  · rw [← hD]
    apply ggOTwoPrime_le_of_map_le_map_of_central_odd_kernel π hπ hodd
    rw [hD, hmap]

theorem ggOTwoPrime_map_fixedFamily_of_central_odd_kernel
    {U V ι : Type*} [Group U] [Finite U] [Group V]
    (π : U →* V) (hπ : π.ker ≤ Subgroup.center U)
    (hodd : Odd (Nat.card π.ker)) (C : Subgroup U)
    (α : ι → MulAut U) (β : ι → MulAut V)
    (hcompat : ∀ i x, π (α i x) = β i (π x)) :
    (ggOTwoPrime (C ⊓ ⨅ i, MonoidHom.eqLocus (α i).toMonoidHom (MonoidHom.id U))).map π =
      ggOTwoPrime (C.map π ⊓ ⨅ i, MonoidHom.eqLocus (β i).toMonoidHom (MonoidHom.id V)) := by
  rw [ggOTwoPrime, ggOTwoPrime, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨⟨hxC, hxfix⟩, k, hxpow⟩, rfl⟩
    refine ⟨⟨Subgroup.mem_map.mpr ⟨x, hxC, rfl⟩, ?_⟩, k, ?_⟩
    · apply Subgroup.mem_iInf.mpr
      intro i
      change β i (π x) = π x
      have hfix := Subgroup.mem_iInf.mp hxfix i
      change α i x = x at hfix
      rw [← hcompat, hfix]
    · rw [← map_pow, hxpow, map_one]
  · rintro ⟨⟨hyC, hyfix⟩, k, hypow⟩
    have hE : IsPGroup 2 (Subgroup.zpowers y) := by
      apply IsPGroup.of_card_dvd_pow (n := k)
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hypow
    have hrange : Subgroup.zpowers y ≤ π.range :=
      Subgroup.zpowers_le_of_mem (Subgroup.map_le_range π C hyC)
    obtain ⟨P, hP, hPmap, _⟩ := CFSG.GroupTheory.exists_isPGroup_map_eq_of_odd hodd hrange hE
    have hPC : P ≤ C := CFSG.GroupTheory.le_of_map_le_map_of_odd hπ hodd hP (by
      rw [hPmap]
      exact Subgroup.zpowers_le_of_mem hyC)
    have hymap : y ∈ P.map π := by rw [hPmap]; exact Subgroup.mem_zpowers y
    obtain ⟨x, hxP, hxy⟩ := Subgroup.mem_map.mp hymap
    obtain ⟨m, hmpow⟩ := hP (⟨x, hxP⟩ : P)
    have hxpow : x ^ 2 ^ m = 1 := congrArg Subtype.val hmpow
    refine ⟨x, ⟨⟨hPC hxP, ?_⟩, m, hxpow⟩, hxy⟩
    apply Subgroup.mem_iInf.mpr
    intro i
    change α i x = x
    have hαpow : (α i x) ^ 2 ^ m = 1 := by rw [← map_pow, hxpow, map_one]
    have hker : x⁻¹ * α i x ∈ π.ker := by
      change π (x⁻¹ * α i x) = 1
      have hfix := Subgroup.mem_iInf.mp hyfix i
      change β i y = y at hfix
      rw [map_mul, map_inv, hcompat, hxy, hfix, inv_mul_cancel]
    exact (CFSG.ProperTwoGeneratedCore.RankOnePair.eq_of_inv_mul_mem_of_central_odd
      hπ hodd hxpow hαpow hker).symm

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem unitaryBlockStandardPair_restrict
    {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    {X : Type} [Group X] {W U V : Subgroup X}
    (h : ClassicalInvolution.Phan.UnitaryBlockStandardPair K p f W U V)
    (N : Subgroup X) (hW : W ≤ N) :
    ClassicalInvolution.Phan.UnitaryBlockStandardPair K p f
      (W.subgroupOf N) (U.subgroupOf N) (V.subgroupOf N) := by
  classical
  obtain ⟨θ, c, hrange, hker, hblocks⟩ := h
  have hN : ∀ g, θ g ∈ N := fun g => hW (hrange ▸ ⟨g, rfl⟩)
  refine ⟨θ.codRestrict N hN, c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map, CFSG.map_codRestrict_eq_subgroupOf θ hN,
      ← MonoidHom.range_eq_map, hrange]
  · rw [MonoidHom.ker_codRestrict]
    exact hker
  · rcases hblocks with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      constructor
      · rw [CFSG.map_codRestrict_eq_subgroupOf θ hN, h1]
      · rw [CFSG.map_codRestrict_eq_subgroupOf θ hN, h2]
    · right
      constructor
      · rw [CFSG.map_codRestrict_eq_subgroupOf θ hN, h1]
      · rw [CFSG.map_codRestrict_eq_subgroupOf θ hN, h2]

end CFSG.StandardType
end
