module

public import CFSG.Quasithin.Vol2.Ch3xC58NSInputs
public import CFSG.Quasithin.Vol2.Ch3xC58NSMPBC127
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Closed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Final
public import CFSG.Quasithin.Background.B15P4Layer2Final
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Holds
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42A57Final
public import CFSG.Quasithin.Background.C129NativeLight
public import CFSG.Quasithin.Background.C1GNBlockLemmas
public import CFSG.Quasithin.Background.C1GNA7
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Blocks.NormOne
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.ClassicalGroups
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.SteinbergBRTwoRankBound
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
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsTitsPair
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245NaturalMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeList
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B1More13
public import CFSG.Quasithin.Background.C58Gamma
public import CFSG.Quasithin.Background.C58IndexTwo
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Quasithin.Vol2.Ch3xC58NSGamma
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Timmesfeld.Final.Orders
public import CFSG.Walter.J1
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.Quasithin.C58NS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

theorem minParabolicBlockSubnormal_of (h113 : Bridge.AsB113With CFSG.SectionRank.IsKGroupCat)
    (hodd : AltEvenExcluded)
    (h123 : ∀ (G : Type) [Group G] [Finite G], L238.C123TwoCgsStatement (G := G))
    (hB42 : ∀ (G : Type) [Group G] [Finite G], L238.AltBlockStatementJCat (G := G))
    (hA7 : ∀ (G : Type) [Group G] [Finite G], L238.C129A7StatementCat (G := G))
    (h38 : Vol2Native.A38ForSQTKCat) : MinParabolicBlockSubnormal := by
  intro G _ _ H T N R P L hminH hchar hSQ _ hRT hTR hRsyl hPX hRP hPN hminP hnc hblk hJ hPeq
  have hTH : T ≤ H := hminH.isSylow.1
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hXH : oTwoUpper H ⊔ R ≤ H := sup_le hKH (hRT.trans hTH)
  have hKT : oTwoUpper H ⊔ T = H := by
    rw [sup_comm, ← F6.twoResidual_eq_oTwoUpper]
    exact sup_twoResidual_eq hminH.isSylow
  have hXn : H ≤ normalizer ((oTwoUpper H ⊔ R : Subgroup G) : Set G) := by
    calc H = oTwoUpper H ⊔ T := hKT.symm
      _ ≤ _ := sup_le (le_sup_left.trans Subgroup.le_normalizer)
        (fun t ht => C1.mem_normalizer_sup (le_normalizer_oTwoUpper H (hTH ht)) (hTR ht))
  have hcharX : CharTwo (oTwoUpper H ⊔ R) := A4.charTwo_of_normal hXH hXn hchar
  have hSQX : CFSG.SectionRank.IsSQTKCat ↥(oTwoUpper H ⊔ R) := by
    obtain ⟨h1, h2⟩ := C1GN.isSQTKTC_iff_sqtkGroup.mp (C1GN.IsSQTKTC.mono hXH hSQ)
    exact ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mpr h1, h2⟩
  have hPu : P ∈ uFamHat (oTwoUpper H ⊔ R) R := by
    refine ⟨⟨hPX, hminP.lt, ?_⟩, hminP.not_normal⟩
    have h : maxOver P R = {P ⊓ N} := hminP.uniqueMax
    rw [h]
    exact Set.ncard_singleton _
  have hcgs : cgsIn (oTwoUpper H ⊔ R) R ≤ N ⊓ (oTwoUpper H ⊔ R) := by
    refine iSup_le fun C => iSup_le fun hCR => iSup_le fun hC1 => iSup_le fun hCc => ?_
    refine le_inf ?_ inf_le_left
    have hTC : T ≤ H ⊓ normalizer (C : Set G) :=
      le_inf hTH (hTR.trans (normalizer_le_normalizer_of_characteristic hCR hCc))
    have hlt : H ⊓ normalizer (C : Set G) < H :=
      lt_of_le_of_ne inf_le_left fun h => hnc C hCR hC1 hCc (h.symm.le.trans inf_le_right)
    exact (inf_le_inf_right _ hXH).trans (hminH.le_of_lt hTC hlt)
  have hLN : ¬ L ≤ N ⊓ (oTwoUpper H ⊔ R) := by
    intro hle
    apply hPN
    rw [hPeq]
    refine sup_le (hRT.trans hminH.le) (conjClosure_le fun r hr x hx => ?_)
    exact (mem_normalizer_iff.mp (Subgroup.le_normalizer (hminH.le (hRT hr))) x).mp (hle hx).1
  have hblkX : IsBlock2 (oTwoUpper H ⊔ R) L :=
    L246C127.MPB.isBlock2_of_chi0Block h113 hodd (h123 G) (hB42 G) (hA7 G) hcharX hRsyl hSQX
      (h38 _ (Vol2Native.SQTKHypCat.quotient_pCore _ hSQX)) hPu hblk hJ hPeq hcgs inf_le_right hLN
  have hLH : L ≤ H := hblkX.2.1.trans hXH
  have hsub : IsSubnormal L H := A3.subnormal_trans (CFSG.Quasithin.IsBlock2.isSubnormal hblkX)
    (IsSubnormal.step hXH ((normal_subgroupOf_iff_le_normalizer hXH).mpr hXn)
      (IsSubnormal.refl H))
  exact ⟨hblkX.1, hLH, (isSubnormal_iff_subgroupOf hLH).mp hsub⟩

theorem minParabolicBlockSubnormal_holds
    : MinParabolicBlockSubnormal :=
  minParabolicBlockSubnormal_of (Bridge.asB113_of_timmesfeld B15P4.asB15Part4)
    L246C127.altEvenExcluded L246.C123.c123_holds (fun _ _ _ => L238.altBlockStatementJCat_holds)
    (fun _ _ _ => L246A7.c129A7_of_inputs
      (Setup.Top.minParabolicBlocks_final Setup.X1.sporadicExclusion_J4_proved)
      (L246C127.c127StatementCat_of_asB113 (Bridge.asB113_of_timmesfeld B15P4.asB15Part4))
      (L246.C123.c123_holds _) L238.altBlockStatementJCat_holds C129Native.a38ForSQTKCat_proved)
    C129Native.a38ForSQTKCat_proved

end CFSG.Quasithin.C58NS
