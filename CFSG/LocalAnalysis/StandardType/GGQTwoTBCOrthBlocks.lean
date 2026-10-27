module

public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
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

public section

namespace CFSG.StandardType

open Polynomial CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
open CFSG.HardMathSupport.Dickson.Bal207.OrthFix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {d : V ≃ₗ[ZMod 2] V}

private theorem three_dvd_card_zmod_two : 3 ∣ Nat.card (ZMod 2) + 1 := by
  rw [Nat.card_zmod]

private theorem X_sub_one_ne_reciprocal_phi (hd : OddOrderIsometry Q 3 d) (hd1 : d ≠ 1) :
    (X - 1 : (ZMod 2)[X]) ≠ reciprocalPolynomial (X ^ 2 + X + 1) := by
  intro h
  have hφ := phi_mem hd three_dvd_card_zmod_two hd1
  have h2 := hd.reciprocal_reciprocal_eq hφ
  rw [← h, reciprocalPolynomial_X_sub_one] at h2
  exact phi_ne h2.symm

private theorem othersSpace_fixed_eq_top_of_not_mem (hd : OddOrderIsometry Q 3 d)
    (hX : (X - 1 : (ZMod 2)[X]) ∉ primaryFactors d.toLinearMap) :
    othersSpace d.toLinearMap (X - 1) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hsum := congrArg (fun f : Module.End (ZMod 2) V => f v)
    (sum_primaryProjection (x := d.toLinearMap) hd.squarefree_minpoly)
  simp only [LinearMap.sum_apply, Module.End.one_apply] at hsum
  rw [← hsum]
  refine Submodule.sum_mem _ fun k hk => ?_
  have hk1 : k ≠ X - 1 := fun e => hX (e ▸ hk)
  exact Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem
    ⟨hk, hk1, by rw [reciprocalPolynomial_X_sub_one]; exact hk1⟩
    (primaryProjection_mem hd.squarefree_minpoly hk v))

private theorem othersSpace_phi_eq_bot_of_not_mem (hd : OddOrderIsometry Q 3 d)
    (hX : (X - 1 : (ZMod 2)[X]) ∉ primaryFactors d.toLinearMap) :
    othersSpace d.toLinearMap (X ^ 2 + X + 1) = ⊥ := by
  rw [eq_bot_iff]
  refine iSup_le fun k => iSup_le fun hk => ?_
  exfalso
  by_cases hkX : k = X - 1
  · exact hX (hkX ▸ hk.1)
  · exact hk.2.1 (eq_phi hd three_dvd_card_zmod_two hk.1 hkX)

private theorem fixedSpace_le_othersSpace_phi (hd : OddOrderIsometry Q 3 d) (hd1 : d ≠ 1) :
    fixedSpace d ≤ othersSpace d.toLinearMap (X ^ 2 + X + 1) := by
  by_cases hX : (X - 1 : (ZMod 2)[X]) ∈ primaryFactors d.toLinearMap
  · rw [fixedSpace_eq_primaryComponent]
    refine le_iSup₂_of_le (X - 1) ⟨hX, ?_, ?_⟩ le_rfl
    · exact fun e => phi_ne e.symm
    · exact X_sub_one_ne_reciprocal_phi hd hd1
  · rw [fixedSpace_eq_bot_of_not_mem hX]
    exact bot_le

theorem ggTBC_block_commute {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {d : V ≃ₗ[ZMod 2] V}
    (hd : OddOrderIsometry Q 3 d) (hd1 : d ≠ 1) {a b : V ≃ₗ[ZMod 2] V}
    (ha : a ∈ supportedBlock Q d (X - 1)) (hb : b ∈ supportedBlock Q d (X ^ 2 + X + 1)) :
    a * b = b * a := by
  have hφ := phi_mem hd three_dvd_card_zmod_two hd1
  by_cases hX : (X - 1 : (ZMod 2)[X]) ∈ primaryFactors d.toLinearMap
  · exact (hd.commute_supportedBlock hX hφ phi_ne
      (by rw [reciprocalPolynomial_X_sub_one]; exact phi_ne) ha hb).eq
  · have ha1 : a = 1 := by
      refine LinearEquiv.ext fun v => ?_
      have hv : a v = v := (mem_supportedBlock.mp ha).2 v (by
        rw [othersSpace_fixed_eq_top_of_not_mem hd hX]
        exact Submodule.mem_top)
      simpa using hv
    rw [ha1, one_mul, mul_one]

theorem ggTBC_block_inf_eq_bot {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {d : V ≃ₗ[ZMod 2] V}
    (hd : OddOrderIsometry Q 3 d) (hd1 : d ≠ 1) :
    supportedBlock Q d (X - 1) ⊓ supportedBlock Q d (X ^ 2 + X + 1) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨hgA, hgB⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨hcompl, -⟩ := hd.fixed_others
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hcompl v
  have hgA' : ∀ x ∈ othersSpace d.toLinearMap (X - 1), g x = x := (mem_supportedBlock.mp hgA).2
  have hgB' : ∀ x ∈ othersSpace d.toLinearMap (X ^ 2 + X + 1), g x = x :=
    (mem_supportedBlock.mp hgB).2
  rw [map_add, hgA' r hr, hgB' w (fixedSpace_le_othersSpace_phi hd hd1 hw)]
  rfl

theorem ggTBC_block_decomp {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {d : V ≃ₗ[ZMod 2] V}
    (hd : OddOrderIsometry Q 3 d) (hd1 : d ≠ 1) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ isometryCentralizer Q d) :
    ∃ a ∈ supportedBlock Q d (X - 1), ∃ b ∈ supportedBlock Q d (X ^ 2 + X + 1), g = a * b := by
  have hφ := phi_mem hd three_dvd_card_zmod_two hd1
  have hgCent : g ∈ Subgroup.centralizer ({d} : Set (V ≃ₗ[ZMod 2] V)) :=
    (Subgroup.mem_inf.mp hg).2
  by_cases hX : (X - 1 : (ZMod 2)[X]) ∈ primaryFactors d.toLinearMap
  ·
    let g' : (Subgroup.centralizer ({d} : Set (V ≃ₗ[ZMod 2] V)) : Subgroup (V ≃ₗ[ZMod 2] V)) :=
      ⟨g, hgCent⟩
    set a : V ≃ₗ[ZMod 2] V := (RankThree.PartOne.KCOrthogonal.blockComponent hd g' (X - 1)).1 with ha_def
    set b : V ≃ₗ[ZMod 2] V := (RankThree.PartOne.KCOrthogonal.blockComponent hd g' (X ^ 2 + X + 1)).1 with hb_def
    have ha : a ∈ supportedBlock Q d (X - 1) := hd.blockComponent_mem hg hX
    have hb : b ∈ supportedBlock Q d (X ^ 2 + X + 1) := hd.blockComponent_mem hg hφ
    obtain ⟨hcompl, -⟩ := hd.fixed_others
    have hRs : othersSpace d.toLinearMap (X - 1) =
        primaryComponent d.toLinearMap (X ^ 2 + X + 1) := othersSpace_eq hd
      three_dvd_card_zmod_two hφ
    have hfixA : ∀ x ∈ othersSpace d.toLinearMap (X - 1), a x = x :=
      (mem_supportedBlock.mp ha).2
    have hfixB : ∀ x ∈ othersSpace d.toLinearMap (X ^ 2 + X + 1), b x = x :=
      (mem_supportedBlock.mp hb).2
    refine ⟨a, ha, b, hb, ?_⟩
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hcompl v
    have hwφ : w ∈ primaryComponent d.toLinearMap (X - 1) := by
      rwa [← fixedSpace_eq_primaryComponent]
    have hrφ : r ∈ primaryComponent d.toLinearMap (X ^ 2 + X + 1) := by
      rwa [← hRs]
    have hbw : b w = w := hfixB w (fixedSpace_le_othersSpace_phi hd hd1 hw)
    have hbr : b r = g r := by
      have h1 := blockComponent_apply_of_mem hd g' (X ^ 2 + X + 1) hφ hrφ
      rw [hb_def]
      simpa [g'] using h1
    have haw : a w = g w := by
      have h1 := blockComponent_apply_of_mem hd g' (X - 1) hX hwφ
      rw [ha_def]
      simpa [g'] using h1
    have hgr : g r ∈ othersSpace d.toLinearMap (X - 1) := by
      rw [hRs]
      exact apply_mem_primaryComponent_of_mem_centralizer hgCent hrφ
    simp only [LinearEquiv.mul_apply, map_add]
    rw [hbw, hbr, hfixA (g r) hgr, haw]
  ·
    have hbot : othersSpace d.toLinearMap (X ^ 2 + X + 1) = ⊥ :=
      othersSpace_phi_eq_bot_of_not_mem hd hX
    refine ⟨1, ?_, g, ?_, by simp⟩
    · exact mem_supportedBlock.mpr ⟨Subgroup.one_mem _, fun _ _ => rfl⟩
    · refine mem_supportedBlock.mpr ⟨hg, fun v hv => ?_⟩
      rw [hbot] at hv
      rw [(Submodule.mem_bot (ZMod 2)).mp hv]
      exact map_zero g

end CFSG.StandardType

end
