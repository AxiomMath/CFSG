module

public import CFSG.LocalAnalysis.StandardType.GGExcCompSLDefs
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
import CFSG.LocalAnalysis.StandardType.GGExcCompSLTypeA
import CFSG.LocalAnalysis.StandardType.GGExcCompSLInner
import CFSG.LocalAnalysis.StandardType.GGExcCompSLOuter
import CFSG.LocalAnalysis.StandardType.GGExcCompSLRankFour
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
import CFSG.ClassicalInvolution.Q3.Q3TWWMinus
import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
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
import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
import CFSG.RankThree.PartOne.KEXC.Basic
import CFSG.RankThree.PartOne.TCX.Ree.Perm
import CFSG.RankThree.PartTwo.Sec8.Item87Proof84

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem langRatCompFieldLenSL_holds
    : LangRatCompFieldLenSL := by
  intro τ L _ _ _ p₀ S hτ p hp hp2 a hT hap h1 i hq
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact langRatFieldSL_typeA S hp hT hap h1 i hA hq
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · exact langRatFieldSL_inner hτ S hp hT hap h1 i hA hinner hq
  have hD : 4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1) →
      GGCompFieldAtSL (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
        (rationalComponent S.ρ S.Γ (rootCharHom a) i) := fun hD => by
    by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
    · exact langRatFieldSL_outerD_high S hp hT hap h1 i ⟨h5, hD.2⟩ hinner hq
    · have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by have := hD.1; omega
      exact langRatFieldSL_outerD_four hτ S hp hp2 hT hap i hr4 (by rw [hD.2, hr4]) hinner hq
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
    have hshape := e6_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact hD hD'
    · exact (false_of_e6Class_E S hp hpL hTp h1 i hE'.1 hE'.2).elim
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL hTp i
    have hshape := e7_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact hD hD'
    · exact langRatFieldSL_outerE (Or.inl rfl) S hp hp2 hT hap i hE' hinner hq
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL hTp i
    have hshape := e8_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact hD hD'
    · exact langRatFieldSL_outerE (Or.inr rfl) S hp hp2 hT hap i hE' hinner hq

end CFSG.StandardType.LangRat
