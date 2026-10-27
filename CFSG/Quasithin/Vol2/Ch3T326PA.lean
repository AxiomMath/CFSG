module

public import CFSG.Quasithin.Background.SmithD321CaseI
public import CFSG.Quasithin.Background.SmithD321Two
public import CFSG.Quasithin.Background.SmithD321Main
public import CFSG.Quasithin.Background.SmithD321CaseIIb
public import CFSG.Quasithin.Background.SmithD321Sym
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
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
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34Size
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma37
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Quasithin.Background.HFF
public import CFSG.Quasithin.Background.HSL3Inner
public import CFSG.Quasithin.Background.SmithB42L2Nat
public import CFSG.Quasithin.Background.SmithB42Sp4Real
public import CFSG.Quasithin.Background.SmithB51LnRealB
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base3
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base4
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base19
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base20
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base21
public import CFSG.Quasithin.Vol2.Ch11SecOE3E
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Open

variable {W : Type} [CommGroup W] [Finite W]

theorem nat_of_ffSide {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    {A : Subgroup (MulAut W)} {r : ℚ} (hS : D321Sit M Mp T L V t A r)
    (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) (hff : FFSide hS.hD.hyp.Mp_normal L)
    (hL3 : IsPSL 3 2 1 ↥L) : BinaryNaturalSL L V (V ⊓ fixV Mp) 3 1 := by
  rcases type_of_ffSide hS hVt hff with ⟨n, hn, hnat⟩ | ⟨-, hnat⟩ | ⟨hA5, -⟩
  · exfalso
    obtain ⟨K, hKf, hKfin, hK, e, -⟩ := exists_equiv_of_binaryNaturalSL hnat
    have : CharP K 2 := FFC.charP_two_of_card_pow hK
    have : Fintype K := Fintype.ofFinite K
    exact not_isPSL_two_of_isPSL32 hL3 (SmithD37.isPSL_of_mulEquiv hn hK e.symm)
  · exact hnat
  · exfalso
    have e1 := card_eq_168_of_isPSL32 hL3
    rw [card_eq_60_of_alt5 hA5] at e1
    norm_num at e1

omit [Finite W] in
theorem isPSL32_conjAutSub {L : Subgroup (MulAut W)} (t : MulAut W) (hL3 : IsPSL 3 2 1 ↥L) :
    IsPSL 3 2 1 ↥(conjAutSub t L) :=
  SmithD37.isPSL_transfer (Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective).symm hL3

theorem exists_natSide_of_d36 (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h9 : A38B42)
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W} {A : Subgroup (MulAut W)}
    {r : ℚ} (hS : D321Sit M Mp T L V t A r) (hc : D36cConcl Mp T L V t)
    (hAC : A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥) (hL3 : IsPSL 3 2 1 ↥L) :
    ∃ (X : Subgroup (MulAut W)) (V' : Subgroup W) (t' : MulAut W),
      D321Sit M Mp T X V' t' A r ∧ (∀ v ∈ V', ∀ g ∈ conjAutSub t' X, g v = v) ∧
      commSub (orbSup T V') X = V' ∧ A ≤ Subgroup.normalizer (X : Set (MulAut W)) ∧
      IsPSL 3 2 1 ↥X ∧ BinaryNaturalSL X V' (V' ⊓ fixV Mp) 3 1 := by
  have hU : commSub (orbSup T V) L = V := by
    by_contra hne
    exact caseIIb_false hS hc hne hAC
  have hVt := hc.1
  have hAL := le_normalizer_of_count hA21 hB42 h9 hS hVt hAC
  rcases ffSide_or hA21 hB42 h9 hS hVt hAC hAL with hff | hff
  · exact ⟨L, V, t, hS, hVt, hU, hAL, hL3, nat_of_ffSide hS hVt hff hL3⟩
  · have hVt' := D321Base.swapV_fix hS.toD321Base hVt
    have hL3' := isPSL32_conjAutSub t hL3
    exact ⟨conjAutSub t L, V.map t.toMonoidHom, t⁻¹, hS.swapV, hVt',
      D321Base.swapV_caseIIa hS.toD321Base hU, le_normalizer_Lt hS hAL, hL3',
      nat_of_ffSide hS.swapV hVt' hff hL3'⟩

theorem exists_natSide (hA21 : AsA21SQTKSection) (hB42 : AsB42)
    (h9 : A38B42) (h36 : D36c) (h37 : D37) (hB56 : AsB56) (h38 : D38Top)
    (hA23 : A23SQTKListFact) (hSzF : H13.SimpleThreePrimeSuzukiFact) (hL38 : D3L38)
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} (hD : D3Std M Mp T L V) {t : MulAut W}
    (htT : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (hqM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ))
    (htop : orbSup T V ≠ ⊤) (hL3 : IsPSL 3 2 1 ↥L) :
    ∃ (X : Subgroup (MulAut W)) (V' : Subgroup W) (t' : MulAut W) (A : Subgroup (MulAut W))
      (r : ℚ), D321Sit M Mp T X V' t' A r ∧ (∀ v ∈ V', ∀ g ∈ conjAutSub t' X, g v = v) ∧
      commSub (orbSup T V') X = V' ∧ A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥ ∧
      A ≤ Subgroup.normalizer (X : Set (MulAut W)) ∧ IsPSL 3 2 1 ↥X ∧
      BinaryNaturalSL X V' (V' ⊓ fixV Mp) 3 1 := by
  have hB := d321Base_of hL38 hD htT htn hMp
  obtain ⟨A, r, hS⟩ := hB.exists_sit hqM htop
  have h3L : 3 ∣ Nat.card ↥L := by
    rw [card_eq_168_of_isPSL32 hL3]
    norm_num
  have hAC := hS.inf_cent_eq_bot_of_three_dvd h38 hA23 hSzF h3L
  have hlt : V < orbSup T V := by
    rcases (le_orbSup T V).eq_or_lt with hVT | hlt
    · exact (caseI_false hB56 h37 hS hVT hAC).elim
    · exact hlt
  rcases h36 W M Mp T L V hD hlt t htT htn hMp with hc | hc
  · obtain ⟨X, V', t', hS', h1, h2, h3, h4, h5⟩ :=
      exists_natSide_of_d36 hA21 hB42 h9 hS hc hAC hL3
    exact ⟨X, V', t', A, r, hS', h1, h2, hAC, h3, h4, h5⟩
  · obtain ⟨X, V', t', hS', h1, h2, h3, h4, h5⟩ :=
      exists_natSide_of_d36 hA21 hB42 h9 hS.swap hc hAC (isPSL32_conjAutSub t hL3)
    exact ⟨X, V', t', A, r, hS', h1, h2, hAC, h3, h4, h5⟩

end CFSG.Quasithin.H13.T326
