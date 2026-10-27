module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Defs
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ExcIndexRee
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ExcIndexTits
import CFSG.GroupTheory.PRankBound
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.Adapters.TauCetiExceptional.ReeCatalog
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.HardMathSupport.Foote.E27.Split
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ExcIndex
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.RankThree.Classical.SteinbergBTHigherUnitaryPrimeSubfield
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfield
public import CFSG.RankThree.PartOne.RF4.FinalSec66
public import CFSG.RankThree.PartOne.S11c.Sec66TModels
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Schreier.TitsOther
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
open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem outerThreeBig_suzuki
    : OuterThreeBigAt (fun i => ∃ m, i = .suzuki m) := by
  rintro K _ _ d hd ⟨e⟩ h4 u _ _
  exfalso
  obtain ⟨i, hv⟩ := d
  obtain ⟨m, rfl⟩ := hd
  have hm : 1 ≤ m := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa only [LieTypeIndex.inStandardRange_iff] using h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmodel : CFSG.Theory.Comparator.SzModel m = CFSG.Open.Sz m :=
    CFSG.Models.benderSzModel_eq_sz m
  let toSz : K ≃* CFSG.Open.Sz m :=
    (e.trans (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv)).trans
      ((MulEquiv.subgroupCongr (hmodel.symm.trans
        (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup m))).symm)
  have hcard : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 (2 * m + 1) (by omega)
  let toBP : K ≃* CFSG.Blueprint.suzukiGroup m (GaloisField 2 (2 * m + 1)) :=
    (toSz.trans (CFSG.ShultStronglyClosedTI.glaSzEquivNative m hm hcard).symm).trans
      (MulEquiv.subgroupCongr
        (CFSG.QuasithinUnique.B1.suzukiGroup_eq_glaSzGroup m
          (GaloisField 2 (2 * m + 1))).symm)
  have h3K : 3 ∣ Nat.card K := by
    by_contra h
    have hle := CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (H := (⊤ : Subgroup K))
      (p := 3) (k := 0) Nat.prime_three (by simpa [Subgroup.card_top] using h)
    omega
  rw [Nat.card_congr toBP.toEquiv, CFSG.LieType.Ree.suzuki_order hcard] at h3K
  have hq : 2 ^ (2 * m + 1) % 3 = 2 := by
    rw [Nat.pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * m + 1) = q at h3K hq
  have hq2 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3K with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    · omega
  · omega

theorem outerThreeBig_tits
    : OuterThreeBigAt (fun i => i = .tits) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout
  obtain ⟨i, hv⟩ := d
  obtain rfl : i = .tits := hd
  have hfin : ∀ d : TitsLieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : TitsLieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin TitsLieIndex.of
  have := hchar TitsLieIndex.of
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_tits TitsLieIndex.of
  have hR : ReeTitsModel K .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl,
      TitsLieIndex.of.1.fixedField, inferInstance, inferInstance,
      (CFSG.TauCetiBridge.ReeF4.card_fixedField_tits _).trans (pow_one 2).symm,
      ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv 0).symm⟩⟩
  obtain ⟨-, -, hO, -⟩ :=
    CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound K 2 1 hR
  let c : Outer K := QuotientGroup.mk' (inner K) u
  have h3 : c ^ 3 = 1 := by
    show QuotientGroup.mk' (inner K) u ^ 3 = 1
    rw [← map_pow, hu3, map_one]
  have h2 : c ^ 2 = 1 := by
    rw [← hO]
    exact pow_card_eq_one'
  have hc : c = 1 := by
    have : c = c ^ 3 * (c ^ 2)⁻¹ := by group
    rw [this, h3, h2]
    simp
  obtain ⟨k, hk⟩ := (QuotientGroup.eq_one_iff (N := inner K) u).1 hc
  exact absurd hk.symm (hout k)

end CFSG.StandardType.FF81.CatQ1

end
