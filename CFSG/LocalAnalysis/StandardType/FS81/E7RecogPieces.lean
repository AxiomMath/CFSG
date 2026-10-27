module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogDefs
public import CFSG.LocalAnalysis.StandardType.FS81.Defs
public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2OverlapRoots
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairChevalley
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Levi
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofWeylWord
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InTorus
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldCenter
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainSetup
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotMain
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwapRee
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicSix
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatOmegaMinusSporadic
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterOmegaExc
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.Monster.B.CTIB.ComponentsSeventeen
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.SPOR.OuterB
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import CFSG.Sporadic.HN.CertificateBase
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate1016Base
public import Certificates.Certificate1021
public import Certificates.Certificate3085Base

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.QuasithinUnique

noncomputable abbrev e7HighInv :
    ↥(adjointGroup .E7 (ZMod 2)) :=
  CFSG.SeitzReduction.EPilot.pinnedElt .E7 (CFSG.SeitzReduction.highRoot .E7) (1 : ZMod 2)

noncomputable abbrev e7JTheta :
    Subgroup ↥(adjointGroup .E7 (ZMod 2)) :=
  (CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2)).subgroupOf (adjointGroup .E7 (ZMod 2))

noncomputable abbrev e7JThetaD6 :
    Subgroup ↥(adjointGroup .E7 (ZMod 2)) :=
  (rootSubgroup .E7 (ZMod 2) CFSG.SeitzReduction.E7Pilot.d6HighRoot ⊔
      rootSubgroup .E7 (ZMod 2) (-CFSG.SeitzReduction.E7Pilot.d6HighRoot)).subgroupOf
    (adjointGroup .E7 (ZMod 2))

@[expose] def HoltSimpleControl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H S : Subgroup G) (z : G),
    IsSimpleGroup ↥H → (∃ a c : ↥H, a * c ≠ c * a) →
    (∀ m : ℕ, 2 ≤ m → 2 * Nat.card ↥H ≠ (2 * m).factorial) →
    IsSylow2In S H → z ∈ S → orderOf z = 2 → (∀ s ∈ S, s * z = z * s) →
    (∀ g : G, g * z * g⁻¹ ∈ H → g ∈ H) → H = ⊤

@[expose] def FS81RadicalOdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y R P : Subgroup X) (b₀ : X),
    Subgroup.centralizer (Y : Set X) ⊓ Y = ⊥ → R ≤ Subgroup.centralizer (Y : Set X) →
    Subgroup.centralizer ({b₀} : Set X) = R ⊔ (Subgroup.centralizer ({b₀} : Set X) ⊓ Y) →
    (∀ N : Subgroup X, IsPGroup 2 N → N ≤ Subgroup.centralizer ({b₀} : Set X) ⊓ Y →
      Subgroup.centralizer ({b₀} : Set X) ⊓ Y ≤ Subgroup.normalizer (N : Set X) → N = ⊥) →
    orderOf b₀ = 3 → b₀ ∈ P → P ≤ Y →
    Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    (∀ t ∈ R, orderOf t = 2 → CharTwo (Subgroup.centralizer ({t} : Set X))) →
    ¬ 2 ∣ Nat.card R

@[expose] def FS81RootO2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y R U L P : Subgroup X) (b₀ b t₀ : X),
    Subgroup.centralizer (Y : Set X) ⊓ Y = ⊥ → R ≤ Subgroup.centralizer (Y : Set X) →
    Subgroup.centralizer ({b₀} : Set X) = R ⊔ (Subgroup.centralizer ({b₀} : Set X) ⊓ Y) →
    ¬ 2 ∣ Nat.card R →
    orderOf t₀ = 2 → t₀ ∈ U → IsPGroup 2 U → U ≤ Y →
    U ≤ Subgroup.centralizer ({t₀} : Set X) → L ≤ Subgroup.centralizer ({t₀} : Set X) →
    L ≤ Subgroup.normalizer (U : Set X) →
    (∀ V : Subgroup X, Subgroup.zpowers t₀ ≤ V → V ≤ U → L ≤ Subgroup.normalizer (V : Set X) →
      V = Subgroup.zpowers t₀ ∨ V = U) →
    (∃ y ∈ Y, b = y * b₀ * y⁻¹) → orderOf b = 3 → b ∈ P → P ≤ L →
    Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    (∀ N : Subgroup X, IsPGroup 2 N →
      N ≤ Subgroup.centralizer ({b} : Set X) ⊓ Subgroup.centralizer ({t₀} : Set X) ⊓ Y →
      Subgroup.centralizer ({b} : Set X) ⊓ Subgroup.centralizer ({t₀} : Set X) ⊓ Y ≤
        Subgroup.normalizer (N : Set X) → N ≤ U) →
    CharTwo (Subgroup.centralizer ({t₀} : Set X)) →
    R = ⊥ ∧ pCoreOf 2 (Subgroup.centralizer ({t₀} : Set X)) = U

@[expose] def E7RootCentStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X) (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y)
    (r : ↥(adjointGroup .E7 (ZMod 2))), r ∈ e7JTheta → orderOf r = 3 →
    Subgroup.centralizer ({((ψ r : ↥Y) : X)} : Set X) ≤ Y →
    (∀ g : X, g * ((ψ r : ↥Y) : X) * g⁻¹ ∈ Y → g ∈ Y) →
    CharTwo (Subgroup.centralizer ({((ψ e7HighInv : ↥Y) : X)} : Set X)) →
    pCoreOf 2 (Subgroup.centralizer ({((ψ e7HighInv : ↥Y) : X)} : Set X)) =
      ((CFSG.SeitzReduction.EPilot.highRadical .E7 (ZMod 2)).map ψ.toMonoidHom).map Y.subtype →
    Subgroup.centralizer ({((ψ e7HighInv : ↥Y) : X)} : Set X) ≤ Y

@[expose] def E7ModelL3 : Prop :=
  (∃ P : Subgroup ↥(adjointGroup .E7 (ZMod 2)), e7JTheta ≤ P ∧
      Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) ∧
    ∃ P : Subgroup ↥(adjointGroup .E7 (ZMod 2)), e7JThetaD6 ≤ P ∧
      P ≤ CFSG.SeitzReduction.EPilot.perpLevi .E7 (ZMod 2) ∧
      Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))

@[expose] def E7ModelConj : Prop :=
  ∃ g : ↥(adjointGroup .E7 (ZMod 2)), e7JTheta.map (MulAut.conj g).toMonoidHom = e7JThetaD6

@[expose] def E7ModelO2 : Prop :=
  ∀ r ∈ e7JThetaD6, orderOf r = 3 → ∀ N : Subgroup ↥(adjointGroup .E7 (ZMod 2)), IsPGroup 2 N →
    N ≤ Subgroup.centralizer ({r} : Set ↥(adjointGroup .E7 (ZMod 2))) ⊓
        Subgroup.centralizer ({e7HighInv} : Set ↥(adjointGroup .E7 (ZMod 2))) →
    Subgroup.centralizer ({r} : Set ↥(adjointGroup .E7 (ZMod 2))) ⊓
        Subgroup.centralizer ({e7HighInv} : Set ↥(adjointGroup .E7 (ZMod 2))) ≤
      Subgroup.normalizer (N : Set ↥(adjointGroup .E7 (ZMod 2))) →
    N ≤ CFSG.SeitzReduction.EPilot.highRadical .E7 (ZMod 2)

@[expose] def E7ModelIrr : Prop :=
  ∀ V : Subgroup ↥(adjointGroup .E7 (ZMod 2)), Subgroup.zpowers e7HighInv ≤ V →
    V ≤ CFSG.SeitzReduction.EPilot.highRadical .E7 (ZMod 2) →
    CFSG.SeitzReduction.EPilot.perpLevi .E7 (ZMod 2) ≤
      Subgroup.normalizer (V : Set ↥(adjointGroup .E7 (ZMod 2))) →
    V = Subgroup.zpowers e7HighInv ∨ V = CFSG.SeitzReduction.EPilot.highRadical .E7 (ZMod 2)

end CFSG.StandardType.FrameRoute.FS81
