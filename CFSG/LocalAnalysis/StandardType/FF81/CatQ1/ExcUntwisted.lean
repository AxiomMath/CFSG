module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Defs
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ExcIndex
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Foote.E27.Split
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
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

public section

namespace CFSG.StandardType.FF81.CatQ1

open TauCeti
open CFSG.HardMathSupport.Malle.E27Lie

theorem outerThreeBig_G2
    : OuterThreeBigAt (fun i => ∃ q, i = .G2 q) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, rfl⟩ := hd
  have h3 : 3 ≤ q.p ^ q.exponent := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using h
  have hm := untwistedModel_of_bridgeAll
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hv e
  refine Or.inl (twentySeven_dvd_fixedSubgroup_of_untwistedModel ?_ hm u hu3 hout)
  intro F _ hF α h3' hα
  exact twentySeven_dvd_fixedSubgroup_G2 q.prime_p q.exponent_pos h3 F hF α h3' hα

theorem outerThreeBig_F4
    : OuterThreeBigAt (fun i => ∃ q, i = .F4 q) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, rfl⟩ := hd
  have hm := untwistedModel_of_bridgeAll
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).f4 q hv e
  refine Or.inl (twentySeven_dvd_fixedSubgroup_of_untwistedModel ?_ hm u hu3 hout)
  intro F _ hF α h3' hα
  exact twentySeven_dvd_fixedSubgroup_F4 q.prime_p q.exponent_pos F hF α h3' hα

theorem outerThreeBig_E7
    : OuterThreeBigAt (fun i => ∃ q, i = .E7 q) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, rfl⟩ := hd
  have hm := untwistedModel_of_bridgeAll
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e7 q hv e
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  refine Or.inl (twentySeven_dvd_fixedSubgroup_of_untwistedModel ?_ hm u hu3 hout)
  intro F _ hF α h3' hα
  exact twentySeven_dvd_fixedSubgroup_E7 q.exponent_pos F hF α h3' hα

theorem outerThreeBig_E8
    : OuterThreeBigAt (fun i => ∃ q, i = .E8 q) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, rfl⟩ := hd
  have hm := untwistedModel_of_bridgeAll
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e8 q hv e
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  refine Or.inl (twentySeven_dvd_fixedSubgroup_of_untwistedModel ?_ hm u hu3 hout)
  intro F _ hF α h3' hα
  exact twentySeven_dvd_fixedSubgroup_E8 q.exponent_pos F hF α h3' hα

end CFSG.StandardType.FF81.CatQ1
