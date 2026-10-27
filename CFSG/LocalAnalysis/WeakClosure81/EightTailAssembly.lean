module

public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorel
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveU3Aut
public import CFSG.LocalAnalysis.WeakClosure81.GapTwoTransport
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapThreeTwo
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFour
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFiveBridge
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapSix
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankL2
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeFirst
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPRefute
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosure
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitMain

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Lem711 W3Thm88)

variable {G : Type} [Group G] [Finite G]

theorem w3Lem85ThreeFirst_and_shape_of_producers (hLie : SpPSULieFacts)
    (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H) (hRU : UnitaryRootCommutatorRank)
    (hL2 : L2IrreducibleRank) (hfact : Orth6MinusOddTranspFact) (hConf : SpURootConfiguration) :
    W3Lem85ThreeFirst G ∧ W3Shape86C G ∧ W3Borel86 G := by
  have hRL := l2RootCommutatorRank_of_irreducible hL2
  have g4 := w3Lem85TwoGap4_holds
  have g6 := w3Lem85TwoGap6_of_fact hfact
  have hdisp : W3Lem85TwoDispatch G :=
    w3Lem85TwoDispatch_of_split h711 hRU hRL w3Lem85TwoGap1_holds w3Lem85TwoGap2_holds
      w3Lem85TwoGap3_holds g4 w3Lem85TwoGap5_holds g6
  have hKT : W3Lem85TwoKT G := w3Lem85TwoKT_of_bad (w3Lem85TwoBad_of_dispatch hdisp)
  have hF' : W3Lem85ThreeFirst' G := w3Lem85ThreeFirst'_holds hLie hRU h711 g4 g6 hKT
  have hB' : W3Borel86' G := w3Borel86'_of_split hConf h711 g4 g6
  exact ⟨w3Lem85ThreeFirst_of_prime hF',
    w3Shape86C_holds h711 hB' (w3Shape86C'_holds h711 g4 g6) hF',
    w3Borel86_of_split hConf h711 g4 g6⟩

end CFSG.LocalAnalysis.WeakClosure81

end
