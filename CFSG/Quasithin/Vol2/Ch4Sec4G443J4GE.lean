module

public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4GB
public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4GD
public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4C
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocMain
public import CFSG.Quasithin.EmptyFaithful.S151CLJ4Hj
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Cases
public import CFSG.Sporadic.J4.LocalOrder
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.PSL2Table.Halves
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphisms
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.ClassicalGroups
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingPrime
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeFive
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLem125
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InPartI2
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.Background.FLcAutMat
public import CFSG.Quasithin.EmptyFaithful.FLcMLEGrp
public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.EmptyFaithful.S151S6B
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.Vol2.Ch4Sec1Lem415
public import CFSG.Quasithin.Vol2.Ch4Sec4L443EFact
public import CFSG.Quasithin.Vol2.Ch4Sec4L443EIn
public import CFSG.Quasithin.Vol2.Ch4Sec4Lem445
public import CFSG.RankThree.PartOne.S10.PlaneContract
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

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
  CFSG.Quasithin.J4M2 CFSG.Quasithin.J4Loc


theorem JM.modelM24_J : @ModelM24 J (Subgroup.toGroup _) := by
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  exact modelM24_of (P0 := P0) (Hj := Hj) (B0 := B0grp) (V0 := V0) (z0 := z0) (card_P0 hM hF)
    (card_J_factorization hF) (exists_conj_le_P0 hM hF)
    (fun x hx => J4Local.eq_one_or_eq_zJ_of_mem_centerOf hx) (JM.not_dvd_card_M2 hF)
    (fun Y hY N hN hne hNY => overgroup_of_normal_two_subgroup j4TwoLocalOvergroups hY hN hne hNY)
    (J4L4.card_V0 hM) (Subgroup.subset_closure (by simp [z0])) (card_Hj hF) (JM.perfectCore_M2 hF)
    (JM.isHat_B0grp hF) (JM.sup_B0grp_eq_top hF)

theorem kg443J4GenM24_holds : KG443J4GenM24 := by
  intro G _ _ K Y V S z hJ hYK hYp hYq hV hV1 hVY hS hzV hz1 hzS
  have hF : J4Facts := j4Facts
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  obtain ⟨e₀⟩ := hJ
  exact @genM24_of_mulEquiv J (Subgroup.toGroup _) _ JM.modelM24_J G _ _ K Y V S z
    (e₀.trans (seedEquiv hF.mat)) hYK hYp hYq hV hV1 hVY hS hzV hz1 hzS

end CFSG.Quasithin.H13.Ch4.G443J4
