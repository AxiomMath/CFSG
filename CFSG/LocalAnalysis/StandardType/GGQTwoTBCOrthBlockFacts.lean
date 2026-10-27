module

public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDickson
public import CFSG.RankThree.Literature.FSmithOrthogonal
public import CFSG.RankThree.PartOne.S11d.OrthLayer
public import CFSG.HardMathSupport.Dickson.Bal207.OrthFixedType
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.RankThree.PartOne.S12.Sec15FA
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate2
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.StandardType

open Polynomial CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.Classical2 CFSG.RankThree.OrthogonalInvolutions

private theorem dicksonDerived_of_six_le_finrank
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {R : QuadraticForm (ZMod 2) W} (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    (h6 : 6 ≤ Module.finrank (ZMod 2) W) :
    CFSG.RankThree.PartOne.DicksonDerived R hR := by
  intro g hg
  have hker : g ∈ (dicksonHom R hR).ker := MonoidHom.mem_ker.mpr hg
  rw [dicksonHom_ker R hR, Subgroup.mem_subgroupOf] at hker
  have hΩ : orthDerived R = omegaGroup R hR :=
    CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hR h6
  rw [hΩ]
  exact hker

theorem ggTBC_orthDerived_inf_block_le {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {d : V ≃ₗ[ZMod 2] V}
    (hd : OddOrderIsometry Q 3 d) (h6 : 6 ≤ Module.finrank (ZMod 2) (fixedSpace d)) :
    orthDerived Q ⊓ supportedBlock Q d (X - 1) ≤ supportedFixedDerived Q d := by
  intro g hg
  obtain ⟨hgΩ, hgF⟩ := Subgroup.mem_inf.mp hg
  have hr : (X - 1 : (ZMod 2)[X]) ∈ primaryFactors d.toLinearMap := by
    by_contra hnot
    have hbot := fixedSpace_eq_bot_of_not_mem hnot
    rw [hbot, finrank_bot] at h6
    omega
  have hodd : Odd 3 := by decide
  have hdick : dicksonHom Q hQ
      ⟨g, orthDerived_le_orthogonalGroup_of_commutator Q hgΩ⟩ = 1 :=
    dicksonHom_apply_orthDerived_eq_one hQ hgΩ
  have hdickW : dicksonHom (Q.comp (fixedSpace d).subtype)
      hd.polarBilin_fixed_nondegenerate
      ⟨isometryRestrictFixed Q d
          ⟨g, supportedBlock_le_isometryCentralizer (X - 1) hgF⟩,
        isometryRestrictFixed_mem_orthogonalGroup _⟩ = 1 := by
    rw [← hd.dicksonHom_eq_restrict_of_mem_supportedBlock hodd hQ hr hgF]
    exact hdick
  refine mem_supportedFixedDerived.mpr ⟨hgF, ?_⟩
  rw [← isometryRestrictFixed_restrictFixed (Q := Q) (x := d) ⟨g, hgF⟩]
  exact dicksonDerived_of_six_le_finrank hd.polarBilin_fixed_nondegenerate h6 _ hdickW

theorem ggTBC_pow_three_mem_specialBlock {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {d : V ≃ₗ[ZMod 2] V}
    (hd : OddOrderIsometry Q 3 d) (hd1 : d ≠ 1) {b : V ≃ₗ[ZMod 2] V}
    (hb : b ∈ supportedBlock Q d (X ^ 2 + X + 1)) :
    b ^ 3 ∈ specialBlock Q d (X ^ 2 + X + 1) := by
  have hmem : (X ^ 2 + X + 1 : (ZMod 2)[X]) ∈ primaryFactors d.toLinearMap := by
    have hpq : 3 ∣ Nat.card (ZMod 2) + 1 := by
      norm_num [Nat.card_zmod]
    exact CFSG.HardMathSupport.Dickson.Bal207.OrthFix.phi_mem hd hpq hd1
  have hirr : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) :=
    irreducible_of_mem_primaryFactors hmem
  have hfact : Fact (Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X])) := ⟨hirr⟩
  have hdeg : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 :=
    (CFSG.HardMathSupport.Dickson.Bal207.OrthFix.monic_phi (K := ZMod 2)).2
  have hfin : Module.Finite (ZMod 2) (AdjoinRoot (X ^ 2 + X + 1 : (ZMod 2)[X])) :=
    (AdjoinRoot.powerBasis (f := (X ^ 2 + X + 1 : (ZMod 2)[X])) hirr.ne_zero).finite
  have hdim : Module.finrank (ZMod 2)
      (AdjoinRoot (X ^ 2 + X + 1 : (ZMod 2)[X])) = 2 := by
    rw [(AdjoinRoot.powerBasis (f := (X ^ 2 + X + 1 : (ZMod 2)[X])) hirr.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim hirr.ne_zero, hdeg]
  have hFin : Finite (AdjoinRoot (X ^ 2 + X + 1 : (ZMod 2)[X])) :=
    Module.finite_of_finite (ZMod 2)
  have hFintype : Fintype (AdjoinRoot (X ^ 2 + X + 1 : (ZMod 2)[X])) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot (X ^ 2 + X + 1 : (ZMod 2)[X])) = 4 := by
    rw [← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := AdjoinRoot (X ^ 2 + X + 1 : (ZMod 2)[X])), hdim, Nat.card_zmod]
    norm_num
  have hunit : IsUnit (blockDet Q d (X ^ 2 + X + 1) ⟨b, hb⟩) := by
    rw [blockDet_apply]
    exact LinearMap.isUnit_det _ (Units.isUnit _)
  have hu3 : blockDet Q d (X ^ 2 + X + 1) ⟨b, hb⟩ ^ 3 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one
      (blockDet Q d (X ^ 2 + X + 1) ⟨b, hb⟩) hunit.ne_zero
    rw [hcard] at h
    simpa using h
  have hS : b ^ 3 ∈ supportedBlock Q d (X ^ 2 + X + 1) := Subgroup.pow_mem _ hb 3
  refine mem_specialBlock.mpr ⟨hS, ?_⟩
  have hpow : (⟨b ^ 3, hS⟩ : ↥(supportedBlock Q d (X ^ 2 + X + 1))) =
      (⟨b, hb⟩ : ↥(supportedBlock Q d (X ^ 2 + X + 1))) ^ 3 := by
    ext
    simp
  rw [hpow, map_pow, hu3]

end CFSG.StandardType

end
