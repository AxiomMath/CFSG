module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4Syl3C
public import CFSG.RankThree.PartTwo.Sec21.FF81F4CenCard
public import CFSG.RankThree.PartTwo.Sec21.FF81F4L3
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsEndNode
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsSylow
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwap
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerActionOuter
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndSwapF4
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
  CFSG.RankThree.PartTwo.Sec21.FF79.L41 CFSG.RankThree.PartTwo.Sec21.FF81
open CFSG.LieType.Simplicity.TitsBits CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.StandardType CFSG.StandardType.TableBF4TwoInputs CFSG.SeitzReduction.F4Pilot

section Cen3


theorem card_cen_rAE :
    Nat.card ↥(Subgroup.centralizer ({rAE} : Set F42C)) = 2 ^ 9 * 3 ^ 5 * 5 * 7 := by
  have hK : Nat.card (ZMod 2) = 2 := by simp
  have hX := centralizer_nonsplit (K := ZMod 2) zpowers_nodeElt_le
    (Subgroup.isCyclic_zpowers _) (card_zpowers_nodeElt hK)
  have h1 := card_sup_eq_mul_of_le_centralizer (Subgroup.le_centralizer_iff.1 hX.2.2)
    (disjoint_iff.1 hX.2.1)
  have h2 : Nat.card ↥(Subgroup.centralizer
      ({nodeElt (ZMod 2)} : Set (adjointGroup .F4 (ZMod 2)))) =
      Nat.card ↥(Subgroup.zpowers (nodeElt (ZMod 2)) ⊔ C3Levi (ZMod 2)) := by
    rw [centralizer_singleton_eq_zpowers]
    exact congrArg (fun H : Subgroup (adjointGroup .F4 (ZMod 2)) => Nat.card ↥H) hX.1
  rw [h1, card_zpowers_nodeElt hK, hK, card_C3Levi_two hK] at h2
  exact h2


theorem card_cen_rBE :
    Nat.card ↥(Subgroup.centralizer ({rBE} : Set F42C)) = 2 ^ 9 * 3 ^ 5 * 5 * 7 := by
  haveI : CharP (ZMod 2) ReeTag.F4.prime := inferInstanceAs (CharP (ZMod 2) 2)
  have h1 := card_cen_isConj phi_link_C
  have h2 := card_cen_aut (ReeTag.F4.finiteExceptionalAut (ZMod 2)) rAE
  exact (h1.symm.trans h2).trans card_cen_rAE

theorem three_pow_dvd_cen_zE :
    3 ^ 6 ∣ Nat.card ↥(Subgroup.centralizer ({zE} : Set F42C)) := by
  haveI : Finite F42C := finite_adjF
  have hle : P0 ≤ Subgroup.centralizer ({zE} : Set F42C) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (zE_central x hx)
  have := Subgroup.card_dvd_of_le hle
  rwa [card_P0, show (729 : ℕ) = 3 ^ 6 by norm_num] at this

theorem L2_star {x : F42C} (hx : orderOf x = 3) :
    3 ^ 6 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set F42C)) ∨
      Nat.card ↥(Subgroup.centralizer ({x} : Set F42C)) = 2 ^ 9 * 3 ^ 5 * 5 * 7 := by
  rcases order_three_cases hx with ⟨c, hcx⟩ | ⟨c, hcx⟩ | ⟨c, hcx⟩
  · right
    rw [card_cen_isConj (isConj_iff.2 ⟨c, hcx⟩)]
    exact card_cen_rAE
  · right
    rw [card_cen_isConj (isConj_iff.2 ⟨c, hcx⟩)]
    exact card_cen_rBE
  · left
    rw [card_cen_isConj (isConj_iff.2 ⟨c, hcx⟩)]
    exact three_pow_dvd_cen_zE

end Cen3

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
