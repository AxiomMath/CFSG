module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.Timmesfeld

theorem card_eq_of_isL3 {X : Type} [Group X] (h : IsL3 X 1) : Nat.card X = 168 := by
  have hc : StatedClassicalModel X .PSL 3 2 1 := LieModel.statedClassicalModel h (by decide)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hc
  rw [Nat.card_congr e.toEquiv, ClassicalOrders.card_statedProj_statedSL (by omega), hK]
  decide +kernel

theorem card_eq_of_isL3_quotient {G : Type} [Group G] {M E : Subgroup G}
    [(E.subgroupOf M).Normal] (hEM : E ≤ M) (h8 : Nat.card E = 8)
    (h : IsL3 (↥M ⧸ E.subgroupOf M) 1) : Nat.card M = 1344 := by
  have hE : Nat.card (E.subgroupOf M) = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv).trans h8
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (E.subgroupOf M), hE,
    card_eq_of_isL3 h]

theorem not_nine_dvd_card_of_isL3 {X : Type} [Group X] (h : IsL3 X 1) : ¬ 9 ∣ Nat.card X := by
  rw [card_eq_of_isL3 h]
  decide

theorem not_nine_dvd_card_of_isL3_quotient {G : Type} [Group G] {M E : Subgroup G}
    [(E.subgroupOf M).Normal] (hEM : E ≤ M) (h8 : Nat.card E = 8)
    (h : IsL3 (↥M ⧸ E.subgroupOf M) 1) : ¬ 9 ∣ Nat.card M := by
  rw [card_eq_of_isL3_quotient hEM h8 h]
  decide

end CFSG.LocalAnalysis.WeakClosure81
