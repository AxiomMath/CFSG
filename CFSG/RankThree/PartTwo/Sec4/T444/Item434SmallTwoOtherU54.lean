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

namespace U54

theorem card_U54 : Nat.card (projSU 5 2 2) = 3 ^ 2 * 5938216960000 :=
  CFSG.PGLModel.card_projSU_five_four.trans (by norm_num)

theorem factorization_card_U54 : (Nat.card (projSU 5 2 2)).factorization 3 = 2 := by
  rw [card_U54]
  exact Item434AltPerm.factorization_three_pow_mul 2 (by norm_num)

theorem center_U54 : Subgroup.center (projSU 5 2 2) = ⊥ := by
  have : IsSimpleGroup (projSU 5 2 2) := Sec21.isSimpleGroup_projSU (by norm_num) (by norm_num)
  exact Item434Spor.center_eq_bot_of_simple (by rw [card_U54]; norm_num)

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_U54 (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* projSU 5 2 2) : False := by
  have := UTools.finite_projSU_gf16 5
  obtain ⟨P, -, hPc, hP⟩ := exists_inner h e outU54_holds center_U54
  have h9 : Nat.card h.layerStar = 9 := by
    rcases h.card_layerStar with h9 | ⟨h27, -⟩
    · exact h9
    · exfalso
      have hd := Subgroup.card_subgroup_dvd_card P
      rw [hPc, h27, card_U54] at hd
      norm_num at hd
  obtain ⟨g, rfl⟩ := exists_map_conj_of_sylow (P₀ := UTools.P₀U 5 (by norm_num))
    (by rw [UTools.card_P₀U, factorization_card_U54]; norm_num)
    (by rw [hPc, h9, UTools.card_P₀U])
  exact false_of_closure_coprime_nine h e center_U54 hP h9
    (closure_coprime_nine_map_conj (UTools.closure_P₀U (by norm_num)) g)

end U54

end Item434SmallTwoOther

section Families


theorem item434SmallTwoOtherAtU54 : Item434SmallTwoOtherAtU54 := by
  intro _ _ _ _ _ G _ _ _ _ _ A M Q hc hL
  obtain ⟨e⟩ := hL
  exact (Item434SmallTwoOther.U54.false_of_U54 hc e).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
