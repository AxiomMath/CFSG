module

public import CFSG.RankThree.PartTwo.Sec12.Hering129GOmega
public import CFSG.RankThree.PartTwo.Sec12.Hering129GST
import CFSG.RankThree.PartTwo.Sec13.OmegaNonempty

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec12.Proof128

@[expose] def HJBranchFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
    (K S : Subgroup G), Cfg129 G A c L b a K S → HJType129 L K → False

theorem hjBranchFalse_of
    (h128 : Item128BarAt) (hNF : KS128NotHJFree) (h422 : Sec4.Item4_22) (h423 : Sec4.Item4_23)
    (hST : Sec21.Item1134E27ST) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (hK2 : KFacts.KS12NormalizerMoves) : HJBranchFalse := by
  intro G _ _ A c L b a K S cfg hHJ
  by_cases hAT : A ∈ partTwoT G
  · obtain ⟨-, -, -, -, -, -, -, -, -, hxD, hxb, hxL, hxB, hxA, hx1⟩ := cfg.point_facts
    have hAe : CFSG.Assembly.IsElemAbelian 3 A := cfg.std.isE27.1
    have hΩ := gap129HJOmega_of G A c L b a K S cfg hHJ (a * b) hxD hxb
    have hxΩ : Subgroup.zpowers (a * b) ∈ Sec13.omegaA A :=
      Sec13.zpowers_mem_omegaA_iff.mpr
        ⟨hxA, Sec13.card_zpowers_eq_three hAe hxA hx1, hΩ⟩
    exact hxL (mem_L_of_omega_ST hNF h422 h423 hST h45 h48 h415 hK2 cfg.std cfg.mem_E cfg.mem_S
      hAT cfg.list hxΩ hxB)
  · exact false_of_hj_branch_notT h128 gap129HJOmega_of cfg hHJ hAT

end CFSG.RankThree.PartTwo.Sec12
