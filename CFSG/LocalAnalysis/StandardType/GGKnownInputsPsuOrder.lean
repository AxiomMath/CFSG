module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExcOrders
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAlt
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
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
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

theorem exists_ppd_dvd_ordTwistedA_five {n : ℕ} (hn : 1 ≤ n) :
    ∃ p, IsPrimitivePrimeDivisor p (10 * n) ∧ p ∣ ordTwistedA 5 (2 ^ n) := by
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 10 * n) (by omega) (by omega)
  refine ⟨p, hp, ?_⟩
  have h := (CFSG.SeitzReduction.UnitaryPilot.profile_idxU (n := 5) (g := n) (by norm_num)
    hn).prim p (10 * n) hp (by omega)
  refine h.2 ⟨5, by simp, Or.inr ⟨by decide, ⟨1, by ring⟩, fun hdvd => ?_⟩⟩
  have := Nat.le_of_dvd (by omega) hdvd
  omega

private theorem not_ten_mul_dvd {g c a : ℕ} (hg : 0 < g) (ha : 0 < a) (ha20 : a < 20)
    (ha10 : a ≠ 10) : ¬ 10 * (g * c) ∣ g * a := by
  intro h
  rw [show 10 * (g * c) = g * (10 * c) by ring] at h
  have h2 : 10 ∣ a := (Dvd.intro c rfl).trans (Nat.dvd_of_mul_dvd_mul_left hg h)
  omega

theorem not_ordTwistedA_five_dvd_ordF4 {g n : ℕ} (hg : 1 ≤ g) (hn : 1 ≤ n) (hgn : g ∣ n) :
    ¬ ordTwistedA 5 (2 ^ n) ∣ ordF4 (2 ^ g) := by
  intro hdvd
  obtain ⟨p, hp, hpU⟩ := exists_ppd_dvd_ordTwistedA_five hn
  obtain ⟨c, rfl⟩ := hgn
  rcases ((CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordF4' hg).prim p (10 * (g * c)) hp
    (by omega)).1 (hpU.trans hdvd) with h | h | h | h
  · exact not_ten_mul_dvd (a := 12) hg (by norm_num) (by norm_num) (by norm_num) h
  · exact not_ten_mul_dvd (a := 8) hg (by norm_num) (by norm_num) (by norm_num) h
  · exact not_ten_mul_dvd (a := 6) hg (by norm_num) (by norm_num) (by norm_num) h
  · exact not_ten_mul_dvd (a := 2) hg (by norm_num) (by norm_num) (by norm_num) h

theorem not_ordTwistedA_five_dvd_ordE6 {g n : ℕ} (hg : 1 ≤ g) (hn : 1 ≤ n) (hgn : g ∣ n) :
    ¬ ordTwistedA 5 (2 ^ n) ∣ ordE6 (2 ^ g) := by
  intro hdvd
  obtain ⟨p, hp, hpU⟩ := exists_ppd_dvd_ordTwistedA_five hn
  obtain ⟨c, rfl⟩ := hgn
  rcases ((CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordE6' hg).prim p (10 * (g * c)) hp
    (by omega)).1 (hpU.trans hdvd) with h | h | h | h | h | h
  · exact not_ten_mul_dvd (a := 12) hg (by norm_num) (by norm_num) (by norm_num) h
  · exact not_ten_mul_dvd (a := 9) hg (by norm_num) (by norm_num) (by norm_num) h
  · exact not_ten_mul_dvd (a := 8) hg (by norm_num) (by norm_num) (by norm_num) h
  · exact not_ten_mul_dvd (a := 6) hg (by norm_num) (by norm_num) (by norm_num) h
  · exact not_ten_mul_dvd (a := 5) hg (by norm_num) (by norm_num) (by norm_num) h
  · exact not_ten_mul_dvd (a := 2) hg (by norm_num) (by norm_num) (by norm_num) h

theorem not_ordTwistedA_five_dvd_ordTwistedF4 {g n : ℕ} (hg : 1 ≤ g) (hn : 1 ≤ n)
    (hgn : g ∣ n) : ¬ ordTwistedA 5 (2 ^ n) ∣ ordTwistedF4 (2 ^ g) := by
  intro hdvd
  obtain ⟨p, hp, hpU⟩ := exists_ppd_dvd_ordTwistedA_five hn
  obtain ⟨c, rfl⟩ := hgn
  rcases ((CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordTwistedF4' hg).prim p (10 * (g * c))
    hp (by omega)).1 (hpU.trans hdvd) with ⟨h, -⟩ | h | ⟨h, -⟩ | h
  · rw [show 2 * (g * 6) = g * 12 by ring] at h
    exact not_ten_mul_dvd (a := 12) hg (by norm_num) (by norm_num) (by norm_num) h
  · exact not_ten_mul_dvd (a := 4) hg (by norm_num) (by norm_num) (by norm_num) h
  · rw [show 2 * (g * 3) = g * 6 by ring] at h
    exact not_ten_mul_dvd (a := 6) hg (by norm_num) (by norm_num) (by norm_num) h
  · exact not_ten_mul_dvd (c := c) (a := 1) hg (by norm_num) (by norm_num) (by norm_num)
      (by rwa [mul_one])

end CFSG.StandardType.SCFourCover

end
