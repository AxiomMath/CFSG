module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseRee
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseRankOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseIndex
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLieCharRankProof
public import CFSG.Open.StatedDefs
public import CFSG.Blueprint.Catalog
import CFSG.Adapters.TauCetiLieModels
import CFSG.Models.Blueprint
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveSzFiveComponent
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3ELinearTwoOddFieldFixed
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
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
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import CFSG.Blueprint.LieModelAPI
import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

private theorem not_isD2LieCharSmall_of_typeA {p r : ℕ} {q : TauCeti.PrimePower} (hr : 4 ≤ r) :
    ¬ CFSG.AGLEmbeddingD2.IsD2LieCharSmall p (TauCeti.LieTypeIndex.A r q) := by
  rintro ⟨q', -, (⟨-, h⟩ | ⟨-, h | h⟩)⟩
  all_goals cases h <;> omega

private theorem not_isD2LieCharSmall_of_typeTwistedA {p r : ℕ} {q : TauCeti.PrimePower}
    (hr : 4 ≤ r) :
    ¬ CFSG.AGLEmbeddingD2.IsD2LieCharSmall p (TauCeti.LieTypeIndex.twistedA r q) := by
  rintro ⟨q', -, (⟨-, h⟩ | ⟨-, h | h⟩)⟩
  all_goals cases h <;> omega

private theorem not_isD2LieCharSmall_of_bigNonLin {p : ℕ} {d : TauCeti.LieTypeIndex}
    (h : BigNonLinIndex45 d) : ¬ CFSG.AGLEmbeddingD2.IsD2LieCharSmall p d := by
  rintro ⟨q, -, (⟨-, hd⟩ | ⟨-, hd | hd⟩)⟩
  · rw [hd] at h; simp [BigNonLinIndex45] at h
  · rw [hd] at h; simp [BigNonLinIndex45] at h
  · rw [hd] at h; simp [BigNonLinIndex45] at h

section Odd


theorem phase45_conclusion_of_lie_odd (hK2 : K45WeylFive) (hK3 : K45FiveRankTwo)
    (hK4 : K45UnitaryThirtyOneGen) {X : Type} [Group X] [Finite X]
    {L A₁ A₂ B T ML : Subgroup X} (hc : PhaseConfig45 L A₁ A₂ B T ML)
    (h5 : CFSG.Open.pRank 5 (⊤ : Subgroup ↥L) ≤ 1) {d : TauCeti.ValidLieTypeIndex}
    (e : ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) (h2 : d.1.characteristic ≠ 2) :
    ∃ (t : StatedLieTag) (n p f : ℕ), (t = .PSL ∨ t = .PSU) ∧ 5 ≤ n ∧ p.Prime ∧ p ≠ 2 ∧
      p ≠ 5 ∧ StatedLieAdmissible t n p f ∧ LieModel L t n p f ∧
      CFSG.Open.pRank 5 L ≤ 1 := by
  rcases phase45_index_cases d h2 with hree | hsmall | hbig | ⟨r, q, hr, hA | hA⟩
  · obtain ⟨m, hm⟩ := hree
    exact (phase45_false_of_reeG2 hc.hLn hc.hCL ⟨m, hm⟩ e hc.hA1 hc.hA2 hc.hA12
      hc.hA12c hc.hcomm).elim
  · by_cases h31 : d.1.characteristic = 31
    · by_cases hrank : RankOneIndex45 d.1
      · exact (phase45_false_of_rankOne_thirtyOne hK4 hc e h31 hrank).elim
      · have h2' : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥L) :=
          hK3 ↥L d ⟨e⟩ h2 (by rw [h31]; norm_num) (Or.inr ⟨h31, hsmall, hrank⟩)
        omega
    · exact (hK2 X L A₁ A₂ B d hc.hLn hc.hCL ⟨e⟩ hsmall h2 h31 hc.hA1 hc.hA2 hc.hA12
        hc.hA12c hc.hB5 hc.hBA1 hc.hBA2 hc.hcomm hc.hlines).elim
  · by_cases h5c : d.1.characteristic = 5
    · have h3 := CFSG.AGLEmbeddingD2.kFactLieCharRank ↥L d ⟨e⟩ 5 (by norm_num) (by norm_num)
        h5c.symm (not_isD2LieCharSmall_of_bigNonLin (p := 5) hbig)
      omega
    · have h2' : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥L) :=
        hK3 ↥L d ⟨e⟩ h2 h5c (Or.inl hbig)
      omega
  · obtain ⟨idx, hv⟩ := d
    subst hA
    rw [TauCeti.LieTypeIndex.characteristic_A] at h2
    have hmodel : LieModel ↥L .PSL (r + 1) q.p q.exponent :=
      (CFSG.Models.lieModel_A r q hv e).toBlueprint (by simp [CFSG.Blueprint.classicalTags])
    have hp5 : q.p ≠ 5 := by
      intro hq5
      have hchar : 5 = (TauCeti.LieTypeIndex.A r q).characteristic := by
        rw [TauCeti.LieTypeIndex.characteristic_A]
        exact hq5.symm
      have h3 := CFSG.AGLEmbeddingD2.kFactLieCharRank ↥L
        ⟨TauCeti.LieTypeIndex.A r q, hv⟩ ⟨e⟩ 5 (by norm_num) (by norm_num) hchar
        (not_isD2LieCharSmall_of_typeA (p := 5) hr)
      omega
    have h5L : CFSG.Open.pRank 5 L ≤ 1 := by
      rwa [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact ⟨.PSL, r + 1, q.p, q.exponent, Or.inl rfl, by omega, q.prime_p, h2, hp5,
      hmodel.admissible, hmodel, h5L⟩
  · obtain ⟨idx, hv⟩ := d
    subst hA
    rw [TauCeti.LieTypeIndex.characteristic_twistedA] at h2
    have hmodel : LieModel ↥L .PSU (r + 1) q.p q.exponent := by
      have hc : TauCeti.ValidLieTypeIndex.characteristic
          ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩ = q.p :=
        TauCeti.LieTypeIndex.characteristic_twistedA r q
      have hf : TauCeti.ValidLieTypeIndex.fieldExponent
          ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩ = q.exponent :=
        TauCeti.LieTypeIndex.fieldExponent_twistedA r q
      simpa only [hc, hf] using
        (CFSG.Models.lieModel_twistedA r q hv e).toBlueprint
          (by simp [CFSG.Blueprint.classicalTags])
    have hp5 : q.p ≠ 5 := by
      intro hq5
      have hchar : 5 = (TauCeti.LieTypeIndex.twistedA r q).characteristic := by
        rw [TauCeti.LieTypeIndex.characteristic_twistedA]
        exact hq5.symm
      have h3 := CFSG.AGLEmbeddingD2.kFactLieCharRank ↥L
        ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩ ⟨e⟩ 5 (by norm_num) (by norm_num) hchar
        (not_isD2LieCharSmall_of_typeTwistedA (p := 5) hr)
      omega
    have h5L : CFSG.Open.pRank 5 L ≤ 1 := by
      rwa [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact ⟨.PSU, r + 1, q.p, q.exponent, Or.inr rfl, by omega, q.prime_p, h2, hp5,
      hmodel.admissible, hmodel, h5L⟩

end Odd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
