module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherKitNine
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherUTools
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import CFSG.Models.PGLOrders
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherKit
import CFSG.GroupTheory.BaerSuzuki
import CFSG.RankThree.PartTwo.Sec21.Item22Tools
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace Item434SmallTwoOther

namespace U44

theorem card_U44 : Nat.card (projSU 4 2 2) = 3 ^ 2 * 113152000 :=
  CFSG.PGLModel.card_projSU_four_four.trans (by norm_num)

theorem factorization_card_U44 : (Nat.card (projSU 4 2 2)).factorization 3 = 2 := by
  rw [card_U44]
  exact Item434AltPerm.factorization_three_pow_mul 2 (by norm_num)

theorem not_three_dvd_card_outer_U44 : ¬ 3 ∣ Nat.card (Outer (projSU 4 2 2)) := fun h3 => by
  have := h3.trans (card_outer_projSU_dvd 4 2 2 (by norm_num) (by norm_num) (by norm_num))
  norm_num at this

theorem center_U44 : Subgroup.center (projSU 4 2 2) = ⊥ := by
  have : IsSimpleGroup (projSU 4 2 2) := Sec21.isSimpleGroup_projSU (by norm_num) (by norm_num)
  exact Item434Spor.center_eq_bot_of_simple (by rw [card_U44]; norm_num)

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_U44 (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* projSU 4 2 2) : False := by
  have := UTools.finite_projSU_gf16 4
  obtain ⟨P, -, hPc, hP⟩ := exists_inner h e not_three_dvd_card_outer_U44 center_U44
  have h9 : Nat.card h.layerStar = 9 := by
    rcases h.card_layerStar with h9 | ⟨h27, -⟩
    · exact h9
    · exfalso
      have hd := Subgroup.card_subgroup_dvd_card P
      rw [hPc, h27, card_U44] at hd
      norm_num at hd
  obtain ⟨g, rfl⟩ := exists_map_conj_of_sylow (P₀ := UTools.P₀U 4 le_rfl)
    (by rw [UTools.card_P₀U, factorization_card_U44]; norm_num)
    (by rw [hPc, h9, UTools.card_P₀U])
  exact false_of_closure_coprime_nine h e center_U44 hP h9
    (closure_coprime_nine_map_conj (UTools.closure_P₀U le_rfl) g)

end U44

end Item434SmallTwoOther

section Families


theorem item434SmallTwoOtherAtU44 : Item434SmallTwoOtherAtU44 := by
  intro _ _ _ _ _ G _ _ _ _ _ A M Q hc hL
  obtain ⟨e⟩ := hL
  exact (Item434SmallTwoOther.U44.false_of_U44 hc e).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
