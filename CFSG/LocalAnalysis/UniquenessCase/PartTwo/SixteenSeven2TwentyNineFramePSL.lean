module

public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.AutL2Facts

theorem s16c167_isPSL_simpleCentreless {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    SimpleCentreless X := by
  have hs : IsSimpleGroup X := SBc11.isSimpleGroup_of_list (Or.inl h)
  haveI := hs
  refine ⟨fun N hN => ?_, fun z hz => ?_, exists_ne 1⟩
  · haveI := hN
    exact hs.eq_bot_or_eq_top_of_normal N
  · have hzc : z ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr (fun g => (hz g).symm)
    rw [SBc11.center_eq_bot_of_list (Or.inl h)] at hzc
    exact Subgroup.mem_bot.mp hzc

theorem s16c167_isPSL_isPerfect {X : Type} [Group X] (h : IsPSL 3 2 1 X) : Group.IsPerfect X := by
  have hs : IsSimpleGroup X := SBc11.isSimpleGroup_of_list (Or.inl h)
  haveI := hs
  refine TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative (fun hcomm => ?_)
  haveI := hcomm
  have hp : (Nat.card X).Prime := Group.is_simple_iff_prime_card.mp hs
  rw [SBc11.card_of_isPSL_three_two h] at hp
  norm_num at hp

theorem s16c167_isPSL_even_card {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    Even (Nat.card X) := by
  rw [SBc11.card_of_isPSL_three_two h]
  decide

theorem s16c167_isPSL_outer_solvable {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    Group.IsSolvable (Outer X) := by
  haveI : Finite X :=
    Nat.finite_of_card_ne_zero (by rw [SBc11.card_of_isPSL_three_two h]; norm_num)
  have hdvd : Nat.card (Outer X) ∣ 2 := by
    have hb := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inl rfl) le_rfl Nat.prime_two le_rfl h).1
    refine hb.trans ?_
    simp [CFSG.RankThree.OuterOrder.determinantParameter]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic (Outer X) := isCyclic_of_card_dvd_prime hdvd
  infer_instance

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
