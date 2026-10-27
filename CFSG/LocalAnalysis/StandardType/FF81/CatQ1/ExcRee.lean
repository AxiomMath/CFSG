module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Defs
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ExcIndexRee
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

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag TauCeti
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions)
open CFSG.HardMathSupport.Malle.E27Lie

theorem outerThreeBig_reeG2
    : OuterThreeBigAt (fun i => ∃ m, i = .reeG2 m) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout
  obtain ⟨i, hv⟩ := d
  obtain ⟨a, rfl⟩ := hd
  have ha : 1 ≤ a := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa [LieTypeIndex.inStandardRange_iff] using h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.reeG2Bridge a hv (GaloisField 3 (2 * a + 1)) hK
  have hrel : ReeTitsRelationModel K .G2 reeG2Perm reeG2Long 3 (2 * a + 1) a :=
    ⟨GaloisField 3 (2 * a + 1), inferInstance, inferInstance, hK, ⟨e.trans φ.symm⟩⟩
  obtain ⟨F, _, _, _, hF, ⟨e₁⟩⟩ := (reeTitsRelationModel_iff .G2 K (2 * a + 1) a).1 hrel
  obtain ⟨e₂⟩ := CFSG.HardMathSupport.Lang.Coordinator.nonempty_derivedCentralQuotient_reeGamma_G2
    (K := F) ha hF
  let θ := e₁.trans e₂
  refine Or.inl ?_
  rw [← CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr θ u]
  refine twentySeven_dvd_fixedSubgroup_smallRee a ha F hF Nat.prime_three (by norm_num) _
    (by rw [← map_pow, hu3, map_one]) fun hin => ?_
  obtain ⟨k, hk⟩ := (CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff θ u).1 hin
  exact hout k hk.symm

theorem outerThreeBig_reeF4
    : OuterThreeBigAt (fun i => ∃ m, i = .reeF4 m) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout
  obtain ⟨i, hv⟩ := d
  obtain ⟨m, rfl⟩ := hd
  have hfin : ∀ d : ReeF4LieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : ReeF4LieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin (ReeF4LieIndex.of m hv)
  have := hchar (ReeF4LieIndex.of m hv)
  have hm : 1 ≤ m := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hhalf : (ReeF4LieIndex.of m hv).toSuzukiReeIndex.halfExponent = m :=
    SuzukiReeIndex.halfExponent_reeF4 m hv
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at e₁
  have hK := CFSG.TauCetiBridge.ReeF4.card_fixedField_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at hK
  have hR : ReeTitsModel K .twistedF4 2 (2 * m + 1) :=
    ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩, m, rfl,
      (ReeF4LieIndex.of m hv).1.fixedField, inferInstance, inferInstance, hK,
      ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv m).symm⟩⟩
  obtain ⟨a, F, _, _, _, hfa, hFcard, ⟨e'⟩⟩ :
      ∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F F4.prime),
        2 * m + 1 = 2 * a + 1 ∧ Nat.card F = 2 ^ (2 * m + 1) ∧
          Nonempty (K ≃* F4.reeGamma F a) := by
    obtain ⟨-, -, -, -, -, -, hmain⟩ :=
      large_Ree_model_field_outer_group_and_inner_involutions K 2 (2 * m + 1) hR
    obtain ⟨-, a, hfa, F, _, _, hFcard, he⟩ := hR
    have : CharP F F4.prime := by
      have : Fintype F := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (p := 2) (f := 2 * m + 1) (by
        rw [← Nat.card_eq_fintype_card, hFcard])
    obtain ⟨⟨e'⟩, -⟩ := hmain a F hfa hFcard he
    exact ⟨a, F, inferInstance, inferInstance, this, hfa, hFcard, ⟨e'⟩⟩
  have ha : 1 ≤ a := by omega
  have hF : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hFcard
  refine Or.inl ?_
  rw [← CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr e' u]
  refine twentySeven_dvd_fixedSubgroup_largeRee ha hF Nat.prime_three (by norm_num) _
    (by rw [← map_pow, hu3, map_one]) fun hin => ?_
  obtain ⟨k, hk⟩ := (CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff e' u).1 hin
  exact hout k hk.symm

end CFSG.StandardType.FF81.CatQ1
