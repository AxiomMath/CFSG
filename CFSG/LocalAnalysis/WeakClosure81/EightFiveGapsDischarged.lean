module

public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelDischarged
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitMain
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveU3Aut
public import CFSG.LocalAnalysis.WeakClosure81.GapTwoTransport
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapThreeTwo
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFiveBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Lem86_1 W3Thm88)

variable {G : Type} [Group G] [Finite G]

theorem w3Lem85TwoDispatch_of_split_discharged_at3
    (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H)
    (hRU : UnitaryRootCommutatorRankAt 3) (hRL : L2RootCommutatorRank)
    (hfact : Orth6MinusOddTranspFact) : W3Lem85TwoDispatch G :=
  w3Lem85TwoDispatch_of_split_at3 h711 hRU hRL w3Lem85TwoGap1_holds w3Lem85TwoGap2_holds
    w3Lem85TwoGap3_holds w3Lem85TwoGap4_holds w3Lem85TwoGap5_holds
    (w3Lem85TwoGap6_of_fact hfact)

theorem w3Lem86_1_of_split_inputs_at3 (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H)
    (hRU : UnitaryRootCommutatorRankAt 3) (hRL : L2RootCommutatorRank)
    (hfact : Orth6MinusOddTranspFact) (h85three : W3Lem85ThreeFirst G) (hsh : W3Shape86C G) :
    W3Lem86_1 G :=
  w3Lem86_1_of_dispatch_inputs (w3Lem85TwoDispatch_of_split_discharged_at3 h711 hRU hRL hfact)
    h85three hsh (w3Borel86_of_split_discharged h711 hfact)

theorem w3Lem86_1_of_split_inputs (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H)
    (hRU : UnitaryRootCommutatorRank) (hRL : L2RootCommutatorRank)
    (hfact : Orth6MinusOddTranspFact) (h85three : W3Lem85ThreeFirst G) (hsh : W3Shape86C G) :
    W3Lem86_1 G :=
  w3Lem86_1_of_split_inputs_at3 h711
    (unitaryRootCommutatorRank_iff_at.1 hRU 3 le_rfl) hRL hfact h85three hsh

end CFSG.LocalAnalysis.WeakClosure81

end
