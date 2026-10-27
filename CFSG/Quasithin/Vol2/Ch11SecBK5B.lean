module

public import CFSG.Quasithin.Vol2.Ch11SecBK5Base17
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base9
public import CFSG.Quasithin.Vol2.Ch11SecBFacts21
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionConjugation
public import CFSG.ClassicalGroups
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.LieType.SteinbergBRSemidirectSL2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.LargeEvenClassification.Delta
public import CFSG.LocalAnalysis.LargeEvenClassification.MinimalNormalFactors
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreLocalIntersections
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreLocality
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch10SecD33
public import CFSG.Quasithin.Vol2.Ch10SecDClA
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Main
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base10
public import CFSG.Quasithin.Vol2.Ch11SecCFacts
public import CFSG.Quasithin.Vol2.Ch11SecDFacts
public import CFSG.Quasithin.Vol2.Ch11SecDFacts3
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartD
public import CFSG.Quasithin.Vol2.Ch11SecSMain
public import CFSG.Quasithin.Vol2.Ch11SecSShape2
public import CFSG.Quasithin.Vol2.Ch11SecSSym2
public import CFSG.Quasithin.Vol2.Ch11SecSSym3
public import CFSG.Quasithin.Vol2.KGNatSL2
public import CFSG.Quasithin.Vol2.KGNatSL3NatFixed
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.Walter.J1
public import CFSG.Walter.JRFacts
public import CFSG.Walter.PSL2Facts
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H13
  CFSG.Quasithin.Vol2.KGNat
open scoped IsMulCommutative

theorem factNPrimeNat_holds : FactNPrimeNat := by
  intro G _ _ L V n hV hn hLV hcomm hnat X hLX hXN
  obtain ⟨_, hSL | hSp | hG2⟩ := hnat
  · obtain ⟨K, _, _, hK, π, h⟩ := hSL
    have : CharP K 2 := charP_two_of_card (by omega) hK
    obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) h
    obtain ⟨Y, hY, hY1, hY2⟩ := K5.exists_nPrime_eq_of_mat (MonoidHom.id _)
      (fun _ _ hab => hab) (fun γ => ⟨γ, rfl⟩)
      (fun γ x => linModelNat_lin _ γ x) hf hLV hcomm hLX hXN
    calc E3.nPrime (autI hV X) = E3.nPrime (autOn X V) := rfl
      _ = E3.nPrime Y := hY
      _ ≤ n := K5.nPrime_le_SL3 hn hK hY1 hY2
  · obtain ⟨K, _, _, hK, π, h⟩ := hSp
    have : CharP K 2 := charP_two_of_card (by omega) hK
    obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) h
    obtain ⟨Y, hY, hY1, hY2⟩ := K5.exists_nPrime_eq_of_mat (MonoidHom.id _)
      (fun _ _ hab => hab) (fun γ => ⟨γ, rfl⟩)
      (fun γ x => linModelNat_lin _ γ x) hf hLV hcomm hLX hXN
    calc E3.nPrime (autI hV X) = E3.nPrime (autOn X V) := rfl
      _ = E3.nPrime Y := hY
      _ ≤ n := K5.nPrime_le_Sp4 hn hK hY1 hY2
  · obtain ⟨K, _, _, hK, π, h⟩ := hG2
    have : CharP K 2 := charP_two_of_card (by omega) hK
    obtain ⟨c₀, hc0, hc1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
    obtain ⟨f, hf⟩ := exists_isCoord (G2Q8.lmG K) h
    obtain ⟨Y, hY, hY1, hY2⟩ := K5.exists_nPrime_eq_of_mat K5.g2Phi K5.g2Phi_injective
      (K5.g2Phi_surjective hc0 hc1) K5.lmG_lin hf hLV hcomm hLX hXN
    calc E3.nPrime (autI hV X) = E3.nPrime (autOn X V) := rfl
      _ = E3.nPrime Y := hY
      _ ≤ n := K5.nPrime_le_G2 hn hK hY1 hY2

end CFSG.Quasithin.Vol2.Ch11.SecB
