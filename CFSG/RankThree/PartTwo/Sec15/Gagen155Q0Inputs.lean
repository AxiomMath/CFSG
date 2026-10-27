module

public import CFSG.RankThree.PartTwo.Sec15.ThmDFront
public import CFSG.RankThree.PartTwo.Sec15.ThmCM2Main
import CFSG.RankThree.PartTwo.Sec15.ThmDA10
import CFSG.RankThree.PartTwo.Sec15.ThmDL3
import CFSG.RankThree.PartTwo.Sec15.ThmDK7
import CFSG.RankThree.PartTwo.Sec15.F153L3KFus

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof155Q0

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

section Certs

theorem mem_scriptQ_of_two_subgroup_of_inputs (hbot : Item145BotS14) (h148 : Item148R)
    (h142 : Concl142S14) (h143 : Concl143S14) (h146 : Item146S14) (h1444 : Item1444S14)
    (hP4 : ThmD.Step148FourKFact) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A), ∀ P : Subgroup G, P ≤ Y → IsPGroup 2 P →
        A ≤ Subgroup.normalizer (P : Set G) → P ∈ scriptQ A (lB A) :=
  ThmD.mem_scriptQ_of_two_subgroup hbot h148 h142 h143 h146
    (ThmC.pCoreOf_mem_scriptQ_of_scriptY0_free h148 h142 h146 h1444 hbot) hP4
    (ThmD.step153D3_of_inputs ThmD.a7CentralizerThreeCycle_holds h142)
    (ThmD.step153D4_of_inputs F153L3K.l3FieldFusionK_holds h142)

end Certs

end CFSG.RankThree.PartTwo.Sec15.Proof155Q0
