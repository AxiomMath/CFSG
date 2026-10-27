module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OppNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup

theorem sylow_le_normalizer_of_ncard_conjSetOf_le_two
    {G : Type} [Group G] [Finite G] {M P L : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P M)
    (hL : L ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC M)
    (hcard : (CFSG.LocalAnalysis.UniquenessCase.UC22.conjSetOf M L).ncard ≤ 2) :
    P ≤ Subgroup.normalizer (L : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx
  obtain ⟨k, hk⟩ := hP.isPGroup.exists_orderOf_eq_pow (⟨x, hx⟩ : P)
  rw [Subgroup.orderOf_mk x hx] at hk
  refine mem_normalizer_of_ncard_conjSetOf_le_two_of_odd_order hcard (hP.le hx) ?_
  rw [hk]
  exact (by norm_num : Odd 3).pow (n := k)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
