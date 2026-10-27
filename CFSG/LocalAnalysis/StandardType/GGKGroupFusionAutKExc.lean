module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAutKCore
public import CFSG.RankThree.PartOne.MB3.OddOutExceptional
public import CFSG.RankThree.PartOne.AUTSL.OddOutRee
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional
public import CFSG.Adapters.TauCetiExceptional.ReeBridge
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartOne.S11d.OutEsix
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.StronglyEmbedded.ParityCriterion
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
public import CFSG.Walter.Ree.Model.JTHyp
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

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.OutStructure
  CFSG.Blueprint CFSG.TauCetiBridge

section Chevalley


theorem ggLieOutRankTwoAt_G2 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) : GGLieOutRankTwoAt ⟨.G2 q, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_G2 q) fun hp2 => ?_
  have hr := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hq : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2 q.p
      q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl, ?_⟩,
      untwistedModel_of_bridge chevalleyBridges.g2 q hv hp2 (MulEquiv.refl _)⟩
    rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hr
    omega
  by_cases hp3 : q.p = 3
  · rw [hp3] at hm ⊢
    exact (outPNice_G2_three Nat.prime_three hm).toChain
  · exact (outPNice_G2_odd q.prime_p hp2 hp3 hm).toChain

theorem ggLieOutRankTwoAt_F4 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.F4 q).Valid) : GGLieOutRankTwoAt ⟨.F4 q, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_F4 q) fun hp2 => ?_
  exact (outPNice_F4_odd q.prime_p hp2 ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
    untwistedModel_of_bridge chevalleyBridges.f4 q hv hp2 (MulEquiv.refl _)⟩).toChain

theorem ggLieOutRankTwoAt_E6 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) (hp5 : 5 ≤ q.p) : GGLieOutRankTwoAt ⟨.E6 q, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_E6 q) fun hp2 => ?_
  exact (outPNice_E6_gen q.prime_p (by omega) hp2 ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
    untwistedModel_of_bridge chevalleyBridges.e6 q hv hp2 (MulEquiv.refl _)⟩).toChain

theorem ggLieOutRankTwoAt_E7 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E7 q).Valid) : GGLieOutRankTwoAt ⟨.E7 q, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_E7 q) fun hp2 => ?_
  exact (outPNice_E7_gen q.prime_p hp2 ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
    untwistedModel_of_bridge chevalleyBridges.e7 q hv hp2 (MulEquiv.refl _)⟩).toChain

theorem ggLieOutRankTwoAt_E8 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E8 q).Valid) : GGLieOutRankTwoAt ⟨.E8 q, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_E8 q) fun hp2 => ?_
  exact (outPNice_E8_gen q.prime_p ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
    untwistedModel_of_bridge chevalleyBridges.e8 q hv hp2 (MulEquiv.refl _)⟩).toChain

theorem ggLieOutRankTwoAt_twistedE6 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hp5 : 5 ≤ q.p) :
    GGLieOutRankTwoAt ⟨.twistedE6 q, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_twistedE6 q)
    fun hp2 => ?_
  exact (outPNice_twistedE6_gen q.prime_p (by omega) ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
    twistedModel_of_bridge chevalleyBridges.twistedE6 q hv hp2 (by decide)
      (MulEquiv.refl _)⟩).toChain

theorem ggLieOutRankTwoAt_trialityD4 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) : GGLieOutRankTwoAt ⟨.trialityD4 q, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_trialityD4 q)
    fun hp2 => ?_
  exact (outPNice_trialityD4_odd q.prime_p hp2 ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
    twistedModel_of_bridge chevalleyBridges.trialityD4 q hv hp2 (by decide)
      (MulEquiv.refl _)⟩).toChain

end Chevalley

section Ree


theorem ggLieOutRankTwoAt_reeG2 (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid) :
    GGLieOutRankTwoAt ⟨.reeG2 m, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_reeG2 m) fun _ => ?_
  have ha : 1 ≤ m := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using h
  have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  obtain ⟨φ⟩ := reeG2Bridge m hv (GaloisField 3 (2 * m + 1)) hK
  have hm : ReeTitsModel (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group .twistedG2 3
      (2 * m + 1) :=
    ⟨⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩, m, rfl,
      GaloisField 3 (2 * m + 1), inferInstance, inferInstance, hK, ⟨φ.symm⟩⟩
  exact (CFSG.RankThree.PartOne.AUTSL.outPNice_twistedG2 Nat.prime_three hm).toChain

end Ree

end CFSG.StandardType
