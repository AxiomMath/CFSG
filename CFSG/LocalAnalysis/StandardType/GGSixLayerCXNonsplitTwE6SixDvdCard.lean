module

public import CFSG.RankThree.PartOne.KE6.Tw6A2A2Case
public import CFSG.HardMathSupport.Lang.SeitzPlane.TwE6FrameLayer
public import CFSG.HardMathSupport.Lang.SeitzPlane.Tw6D4LayerData
public import CFSG.RankThree.PartOne.D4RC.RxOrder
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.F4ThreeOdd
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.RankThree.Chevalley.SteinbergBID4TrialityDescent
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
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate117
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicLocalCore
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2Case
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.D4RC.RxIso
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourData
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE6.Phi3D4Case
public import CFSG.RankThree.PartOne.KE6.Phi3Frame
public import CFSG.RankThree.PartOne.KE6.Phi3Torsion
public import CFSG.RankThree.PartOne.KE6.Phi6Decomp
public import CFSG.RankThree.PartOne.KE6.Phi6Excl
public import CFSG.RankThree.PartOne.KE6.Phi6Frame
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import CFSG.RankThree.PartOne.KGD.D4QFrame
public import CFSG.RankThree.PartOne.KGD.D4T36Frame
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

namespace CFSG.StandardType.TwE6Nonsplit

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.Lattice (e6T3W)
open scoped Matrix MatrixGroups Pointwise


variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem tw6_A2_layer_card {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {S : Set (Fin Tag.E6.rank → ℤ)} (hSroots : ∀ α ∈ S, IsRoot Tag.E6 α)
    (hvS : ∀ α ∈ S, e6T3W • α ∈ S) {w : WeylGroup Tag.E6}
    (hw : (w • ·) '' S = parabolicRoots Tag.E6 support13) :
    Nat.card ↥(rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr)) =
      (ℓ ^ f) ^ 3 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) := by
  rw [twistedFixedPoints_tw6N]
  obtain ⟨Φ, ⟨e⟩, ⟨H, hH⟩, -⟩ :=
    CFSG.HardMathSupport.Lang.SeitzPlane.tw6_A2_layer_equiv (K := K) (Ω := Ω) hf hK hFr
      hSroots hvS hw
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.RankThree.PartOne.D4RC.rcl_card_fix_unitary (L := Ω) (k := K)
    (Fact.out : ℓ.Prime) hf hK Φ H hH

theorem tw6_D4_layer_card {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {x : ModGL Tag.E6 Ω} (hx : x ∈ twistedTorusOf (tw6N Ω) (twistE6 Ω Fr))
    {w : WeylGroup Tag.E6}
    (hw : (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 d4Support) :
    Nat.card ↥(rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
        twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr)) =
      (ℓ ^ f) ^ 12 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 6 - 1) *
        ((ℓ ^ f) ^ 8 + (ℓ ^ f) ^ 4 + 1) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨-, -, -, -, -, e, g, he, -, ⟨hequiv⟩⟩ :=
    CFSG.HardMathSupport.Lang.SeitzPlane.tw6_D4_layer_data' (K := K) (Ω := Ω) (Fr := Fr)
      hf hK hFr hx hw
  rw [Nat.card_congr hequiv.toEquiv]
  have hk₃ := natCard_cubicSubfield (Ω := Ω) (ℓ := ℓ) hf
  have : IsAlgClosure (cubicSubfield (Ω := Ω) ℓ f) Ω :=
    ⟨inferInstance, isAlgebraic_cubicSubfield (K := K) hK⟩
  have : CharP (cubicSubfield (Ω := Ω) ℓ f) ℓ := inferInstance
  let σ : cubicSubfield (Ω := Ω) ℓ f →+* cubicSubfield (Ω := Ω) ℓ f :=
    iterateFrobenius (cubicSubfield (Ω := Ω) ℓ f) ℓ (f * e)
  have hσ : ∀ c, σ c = c ^ ((ℓ ^ f) ^ e) := fun c => by
    rw [iterateFrobenius_def, pow_mul]
  obtain ⟨φ, -⟩ := exists_d4ThetaFixed_equiv (K := cubicSubfield (Ω := Ω) ℓ f) (Ω := Ω)
    (σ := σ) (Fr := Fr) hℓ hf hk₃ he hσ hFr
  rw [Nat.card_congr φ.toEquiv]
  exact (triality_both_orientations_exact_finite_order ℓ f hℓ hf
    (cubicSubfield (Ω := Ω) ℓ f) hk₃ e he σ hσ).1

theorem dvd_card_trialityD4_of_dvd_phiSix {p q : ℕ} (hq : 1 ≤ q)
    (h : p ∣ q ^ 2 - q + 1) :
    p ∣ q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1) := by
  have hfac : q ^ 6 - 1 = (q ^ 3 - 1) * (q + 1) * (q ^ 2 - q + 1) := by
    have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
    have h2 : q ≤ q ^ 2 := by nlinarith
    zify [hq, h2, h3, h6]
    ring
  obtain ⟨k, hk⟩ := h
  refine ⟨q ^ 12 * (q ^ 2 - 1) * ((q ^ 3 - 1) * (q + 1)) *
    (q ^ 8 + q ^ 4 + 1) * k, ?_⟩
  rw [hfac, hk]
  ring

end CFSG.StandardType.TwE6Nonsplit
