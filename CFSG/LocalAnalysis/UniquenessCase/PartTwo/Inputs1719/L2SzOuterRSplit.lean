module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OuterRSplit
public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
public import CFSG.Quasithin.Vol2.Ch11SecE3LieSL2
public import CFSG.ClassicalInvolution.AschTight.S19COrd
public import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting
public import CFSG.LieType.Ree.SuzukiSplitTorusCentralizers
public import CFSG.LieType.Ree.SuzukiBorelStructure
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.ComponentClassification
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsSz)

theorem outerRSplit_one_of_isL2 {X : Type} [Group X] {n r : ℕ} (hX : IsL2 X n)
    (hr : r.Prime) (hrn : r ∣ 2 ^ n - 1) : OuterRSplit X r 1 := by
  obtain ⟨-, K, hKf, hKfin, hcp, hcard, ⟨e⟩⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecE3.exists_sl2_of_isPSL22
      ((CFSG.Blueprint.LieModel.classical_iff (by decide)).1 hX)
  letI := hKf
  letI := hKfin
  have := hcp
  refine (outerRSplit_one_of_normalForm hr (CFSG.RankThree.PartOne.KCRootAxis.slFieldAut K)
    (fun α _ _ => CFSG.RankThree.PartOne.KCRootAxis.exists_conj_mul_slFieldAut α)
    (fun σ hσ => ?_) ?_).of_mulEquiv e.symm
  · obtain ⟨M, hM⟩ := hσ
    refine (CFSG.RankThree.PartOne.KCRootAxis.conj_mul_slFieldAut_inj (M := M) (M' := 1)
      (σ := 1) (σ' := σ) ?_).2.symm
    simp only [map_one, mul_one, one_mul]
    exact hM
  · rw [CFSG.ClassicalInvolution.Disconnected.AschTight.S19C.card_sl2, hcard]
    have h1 : 2 ^ n - 1 ∣ (2 ^ n) ^ 2 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow (x := 2 ^ n) (y := 1) (n := 2)
    exact Dvd.dvd.mul_left (hrn.trans h1) _

theorem outerRSplit_one_of_isSz {X : Type} [Group X] {n r : ℕ}
    (hX : IsSz X n) (hr : r.Prime) (hrn : r ∣ 2 ^ n - 1) : OuterRSplit X r 1 := by
  obtain ⟨-, a, ha, K, hKf, hKfin, hn, hcard, ⟨e⟩⟩ := (LieModel.suzukiModel hX).2
  letI := hKf
  letI := hKfin
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hn ▸ hcard
  obtain ⟨-, ⟨E, hE⟩, -⟩ :=
    CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha K hK'
  refine (outerRSplit_one_of_normalForm hr
    (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut a K)
    (fun α _ _ => ?_) (fun σ hσ => ?_) ?_).of_mulEquiv e.symm
  · obtain ⟨⟨x, τ⟩, hxτ⟩ := E.surjective α
    exact ⟨x, τ, by rw [← hxτ, hE]⟩
  · obtain ⟨y, hy⟩ := hσ
    have h1 : E ⟨y, 1⟩ = E ⟨1, σ⟩ := by
      rw [hE, hE, map_one, mul_one, map_one, one_mul]
      exact hy
    exact (congrArg SemidirectProduct.right (E.injective h1)).symm
  · have : Fact r.Prime := ⟨hr⟩
    obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r
      (by rw [Nat.card_units, hcard]; exact hrn)
    let D : Kˣ →* CFSG.Blueprint.suzukiGroup a K :=
      { toFun := CFSG.LieType.Ree.suzukiDElt a K
        map_one' := CFSG.LieType.Ree.suzukiDElt_one
        map_mul' := fun l m => (CFSG.LieType.Ree.suzukiDElt_mul l m).symm }
    have hD : Function.Injective D := CFSG.LieType.Ree.suzukiDElt_injective hK'
    rw [← hl, ← orderOf_injective D hD l]
    exact orderOf_dvd_natCard _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
