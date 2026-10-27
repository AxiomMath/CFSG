module

public import CFSG.RankThree.GF2n.Item310
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.Adapters.TauCetiExceptional.EvenInterface
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
import CFSG.Adapters.TauCetiExceptional.EvenBridgeE6E7
import CFSG.Adapters.TauCetiExceptional.EvenBridgeE8
import CFSG.Adapters.TauCetiExceptional.EvenBridgeTwistedE6
import CFSG.Adapters.TauCetiExceptional.EvenD4
import CFSG.StronglyEmbedded.Catalog.Suzuki
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.Adapters.TauCetiExceptional.Interface
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import Certificates.Certificate110
public import Certificates.Certificate43
import CFSG.LieType.Chevalley.EvenRootCommutatorF4
import CFSG.LieType.Universal.Spin.Roots
import CFSG.LieType.Universal.SpinOmega
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.StronglyEmbedded.ParityCriterion
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.RankThree.GF2n

open CFSG.Assembly.LowTwoRank CFSG.Blueprint TauCeti

theorem pOmegaPlusBridge : POmegaPlusBridge := by
  intro G _ n p f hn h
  obtain ⟨hp, hf, -⟩ := h.1
  let q : PrimePower := ⟨p, f, hp, hf⟩
  have hv : (LieTypeIndex.D n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  obtain ⟨e⟩ := EvenSource.nonempty_mulEquiv_of_statedClassicalModel h
    (PartTwo.Census.statedClassicalModel_typeD n q hv (MulEquiv.refl _))
  exact ⟨.lie ⟨_, hv⟩, ⟨e⟩⟩

theorem pOmegaMinusBridge : POmegaMinusBridge := by
  intro G _ n p f hn h
  obtain ⟨hp, hf, -⟩ := h.1
  let q : PrimePower := ⟨p, f, hp, hf⟩
  have hv : (LieTypeIndex.twistedD n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  obtain ⟨e⟩ := EvenSource.nonempty_mulEquiv_of_statedClassicalModel h
    (PartTwo.Census.statedClassicalModel_typeTwistedD n q hv (MulEquiv.refl _))
  exact ⟨.lie ⟨_, hv⟩, ⟨e⟩⟩

@[expose] def evenPrimePower (f : ℕ) (hf : 1 ≤ f) : PrimePower := ⟨2, f, Nat.prime_two, hf⟩

theorem evenPrimePower_p (f : ℕ) (hf : 1 ≤ f) : (evenPrimePower f hf).p = 2 := rfl

theorem evenPrimePower_card (f : ℕ) (hf : 1 ≤ f) : (evenPrimePower f hf).card = 2 ^ f := by
  rw [PrimePower.card_def]
  rfl

theorem inCatalog_of_untwistedChevalleyModel {τ : Chevalley.Tag} {c : PrimePower → LieTypeIndex}
    (hb : TauCetiBridge.Even.UntwistedBridgeEven τ c) {G : Type} [Group G] {f : ℕ} (hf : 1 ≤ f)
    (hv : (c (evenPrimePower f hf)).Valid) (h : UntwistedChevalleyModel G τ (2 ^ f)) :
    Assembly.InCatalog G := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨b⟩ := hb _ hv (evenPrimePower_p f hf) K (hK.trans (evenPrimePower_card f hf).symm)
  exact ⟨.lie ⟨_, hv⟩, ⟨e.trans b⟩⟩

theorem inCatalog_of_twistedChevalleyModel {t : Chevalley.TwistTag}
    {c : PrimePower → LieTypeIndex} (hb : TauCetiBridge.Even.TwistedBridgeEven t c) {G : Type}
    [Group G] {f : ℕ} (hf : 1 ≤ f) (hv : (c (evenPrimePower f hf)).Valid)
    (h : TwistedChevalleyModel G t (2 ^ f)) : Assembly.InCatalog G := by
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  obtain ⟨b⟩ := hb _ hv (evenPrimePower_p f hf) K (by rw [evenPrimePower_card]; exact hK) σ
    (by rw [evenPrimePower_card]; exact hσ)
  exact ⟨.lie ⟨_, hv⟩, ⟨e.trans b⟩⟩

theorem chevalleyEvenBridge_G2 :
    ChevalleyEvenBridge .G2 := by
  rintro G _ f ⟨⟨-, hf, -, h3⟩, h⟩
  refine inCatalog_of_untwistedChevalleyModel TauCetiBridge.Even.untwistedBridgeEven_G2 hf
    ((LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩) h
  · rw [LieTypeIndex.inStandardRange_iff]
    show 3 ≤ (evenPrimePower f hf).card
    rw [evenPrimePower_card]
    exact h3
  · rw [LieTypeIndex.isDuplicateRepresentative_iff]
    exact not_false

theorem chevalleyEvenBridge_E6 :
    ChevalleyEvenBridge .E6 := by
  rintro G _ f ⟨⟨-, hf, -⟩, h⟩
  exact inCatalog_of_untwistedChevalleyModel TauCetiBridge.Even.untwistedBridgeEven_E6 hf
    (LieTypeIndex.valid_E6 _) h

theorem chevalleyEvenBridge_E7 :
    ChevalleyEvenBridge .E7 := by
  rintro G _ f ⟨⟨-, hf, -⟩, h⟩
  exact inCatalog_of_untwistedChevalleyModel TauCetiBridge.Even.untwistedBridgeEven_E7 hf
    (by simp) h

theorem chevalleyEvenBridge_E8 :
    ChevalleyEvenBridge .E8 := by
  rintro G _ f ⟨⟨-, hf, -⟩, h⟩
  exact inCatalog_of_untwistedChevalleyModel TauCetiBridge.Even.untwistedBridgeEven_E8 hf
    (by simp) h

theorem chevalleyEvenBridge_twistedE6 :
    ChevalleyEvenBridge .twistedE6 := by
  rintro G _ f ⟨⟨-, hf, -⟩, h⟩
  exact inCatalog_of_twistedChevalleyModel TauCetiBridge.Even.twistedBridgeEven_twistedE6 hf
    (LieTypeIndex.valid_twistedE6 _) h

theorem chevalleyEvenBridge_trialityD4 :
    ChevalleyEvenBridge .trialityD4 := by
  rintro G _ f ⟨⟨-, hf, -⟩, h⟩
  exact inCatalog_of_twistedChevalleyModel TauCetiBridge.Even.twistedBridgeEven_trialityD4 hf
    (LieTypeIndex.valid_trialityD4 _) h

theorem suzukiBridge : SuzukiBridge := by
  intro G _ f h
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  have hv : (LieTypeIndex.suzuki a).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨ha, not_false⟩
  exact ⟨.lie ⟨_, hv⟩, ⟨(e.trans
    (ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK)).trans
    (BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv).symm⟩⟩

end CFSG.RankThree.GF2n
