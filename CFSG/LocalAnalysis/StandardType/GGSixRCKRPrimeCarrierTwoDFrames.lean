module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDMainG
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.TwistedPairs
public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusBridge
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPReduction
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyFG
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighDefs
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.CTP.SU4EvenBridge
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate10050
public import Certificates.Certificate16005
public import Certificates.Certificate16041
public import Certificates.Certificate17002
public import Certificates.Certificate17951
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2323
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8117
public import Certificates.Certificate9124

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal.Spin
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDMain
open scoped MatrixGroups


theorem rckTwoD_dFrames
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀)
    (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hcard : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    {m : ℕ} (ε : simpleRoots (componentRoots (rootCharHom a) i) ≃ Fin m)
    (hε : ∀ β γ : simpleRoots (componentRoots (rootCharHom a) i),
      corootPair (β : Fin τ.rank → ℤ) γ = cartanD m (ε β) (ε γ))
    (j k : Fin m) (hjk : cartanD m j k = -1) :
    ∃ θ : SL(3, L) →* ModGL τ L,
      θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (ε.symm j) ∧
      θ.comp (blockSL L 3 2 1 (by omega)) = rootSL2 τ L (ε.symm k) := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact exists_dFrames (Or.inl rfl) kacD4 facts_D4 d4_tree d4_adj d4_check d4_lt d4_card
      d4_dcount d4_dtrees (fun {F} _ x y h => d4_frames x y h) S hp hpL hTp i h4 hcard ε hε L j k hjk
  · exact exists_dFrames (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card
      e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hp hpL hTp i h4 hcard ε hε L j k hjk
  · exact exists_dFrames (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt
      e7_card e7_dcount e7_dtrees (fun {F} _ x y h => e7_frames x y h) S hp hpL hTp i h4 hcard ε hε L j k hjk
  · exact exists_dFrames (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt
      e8_card e8_dcount e8_dtrees (fun {F} _ x y h => e8_frames x y h) S hp hpL hTp i h4 hcard ε hε L j k hjk

end CFSG.StandardType.RCKRP
