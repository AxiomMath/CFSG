module

public import CFSG.LocalAnalysis.StandardType.GGLangRatCompTorusLift
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
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660

import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgRank4B
import CFSG.LocalAnalysis.StandardType.GGCompFieldLieModel
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
import CFSG.ClassicalInvolution.Q3.Q3TWWMinus
import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.RankThree.PartOne.KEXC.Basic
import CFSG.RankThree.PartOne.TCX.Ree.Perm
import CFSG.RankThree.PartTwo.Sec8.Item87Proof84

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

open CFSG CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KD4L CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.Yardstones.Md0ec50421ce4 CFSG.RankThree.PartOne.KE6
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.CatLeafProof CFSG.LocalAnalysis.GLTheoremA.K155X
open scoped Matrix MatrixGroups

theorem langRatField_outerD_four
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    GGCompFieldAt (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  have hℓp : ringChar L ≠ p := by
    rw [ringChar.eq L 2]
    exact fun h => hp2 h.symm
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp : rootDiagUnit τ a ^ p = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  have hq' : CFSG.Open.IsQuasisimple
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    ⟨hq.1.commutator_eq_top, hq.2.1⟩
  rcases hτ with rfl | rfl
  · obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four
      (by decide) (by decide)
      (fun y hy => far_d4_E7 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
    obtain ⟨w, hn⟩ := S.D.n_weyl
    have hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
      componentOrbitLength_eq_one
        ((finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1) hρ
    obtain ⟨f, hf, hM⟩ := l154r4_rationalComponent_of_d4_outer d4Base_E7
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 (d4SwapLayer_E7 e6FixDNAll_proved)
      l154r4_trialityLayer_E7 l154r4_swapLayer_E7 S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hout
    rw [ringChar.eq L 2] at hf hM
    rw [hs, pow_one, ← hf]
    rcases hM with hm | hm
    · exact ggCompFieldAt_of_lieModel hq' hm ⟨by decide, by decide, by decide⟩
    · exact ggCompFieldAt_of_lieModel hq' hm ⟨by decide, by decide, by decide⟩
  · obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four
      (by decide) (by decide)
      (fun y hy => far_d4_E8 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
    obtain ⟨w, hn⟩ := S.D.n_weyl
    have hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
      componentOrbitLength_eq_one
        ((finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1) hρ
    obtain ⟨f, hf, hM⟩ := l154r4_rationalComponent_of_d4_outer d4Base_E8
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8 (d4SwapLayer_E8 e6FixDNAll_proved)
      l154r4_trialityLayer_E8 l154r4_swapLayer_E8 S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hout
    rw [ringChar.eq L 2] at hf hM
    rw [hs, pow_one, ← hf]
    rcases hM with hm | hm
    · exact ggCompFieldAt_of_lieModel hq' hm ⟨by decide, by decide, by decide⟩
    · exact ggCompFieldAt_of_lieModel hq' hm ⟨by decide, by decide, by decide⟩

end CFSG.StandardType.LangRat
