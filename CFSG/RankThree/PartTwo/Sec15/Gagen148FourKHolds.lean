module

public import CFSG.RankThree.PartTwo.Sec15.Gagen148FourK
public import CFSG.RankThree.PartTwo.Sec15.Gagen155Q0Inputs
public import CFSG.RankThree.PartTwo.Sec14.Ronan149Holds
public import CFSG.RankThree.PartTwo.Sec15.Gagen155Q0
public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofQ0

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof148FourK

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14


theorem step148FourKFact_holds
    : ThmD.Step148FourKFact := by
  obtain ⟨-, h48, -, -, -, h415, -, -, h134, -, -⟩ := Ronan148M.closedInputs
  exact step148FourKFact_of_steps h134 h48 h415 Ronan148C.step148Core_holds
    Ronan148M.step148Point_holds Ronan148M.step148KType_holds Ronan148M.step148Lift_holds
    Ronan148M.step148D4_holds

section Q0


theorem item146S14_holds
    : Item146S14 :=
  item146_forall_of_concl Ronan148M.concl142S14_holds Ronan148M.concl143S14_holds

theorem mem_scriptQ_of_two_subgroup_holds
    :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A), ∀ P : Subgroup G, P ≤ Y → IsPGroup 2 P →
        A ≤ Subgroup.normalizer (P : Set G) → P ∈ scriptQ A (lB A) :=
  Proof155Q0.mem_scriptQ_of_two_subgroup_of_inputs Ronan149.item145BotS14_holds
    Ronan148M.item148R_holds Ronan148M.concl142S14_holds Ronan148M.concl143S14_holds
    item146S14_holds Ronan149.item1444S14_holds step148FourKFact_holds

theorem step155YQ0WR_holds
    : Step155YQ0WR :=
  Proof155Q0.step155YQ0WR_of_front item146S14_holds mem_scriptQ_of_two_subgroup_holds

theorem step155PJQ0WR_holds
    : Step155PJQ0WR :=
  Proof155Q0.step155PJQ0WR_of_front item146S14_holds mem_scriptQ_of_two_subgroup_holds

theorem step155YQ0HypWR_holds
    : Step155YQ0HypWR :=
  step155YQ0HypWR_of step155YQ0WR_holds

theorem step155PJQ0HypWR_holds
    : Step155PJQ0HypWR :=
  step155PJQ0HypWR_of step155PJQ0WR_holds

end Q0

end CFSG.RankThree.PartTwo.Sec15.Proof148FourK
