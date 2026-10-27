module

public import CFSG.Sporadic.SuzOddCore.InvGraphBound

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

theorem CTUC_Suz_involution_graph_centralizer_bounds :
    (∀ g ∈ suzT, ∀ x y : Fin 1782, invGraph.Adj (g x) (g y) ↔ invGraph.Adj x y) ∧
    (∀ x : Fin 1782, {y | invGraph.Adj x y}.ncard = 416) ∧
    Nat.card (autCent (suzInv 0)) ≤ 322560 ∧ Nat.card (autCent (suzInv 1)) ≤ 6635520 ∧
    Nat.card (autCent (suzInv 2)) ≤ 380160 ∧ Nat.card (autCent (suzInv 3)) ≤ 2419200 ∧
    Nat.card (Subgroup.centralizer {suzInv 0} ⊓ suzT : Subgroup (Equiv.Perm (Fin 1782))) ≤
      322560 ∧
    Nat.card (Subgroup.centralizer {suzInv 1} ⊓ suzT : Subgroup (Equiv.Perm (Fin 1782))) ≤
      6635520 ∧
    Nat.card (Subgroup.centralizer {suzInv 2} ⊓ suzT : Subgroup (Equiv.Perm (Fin 1782))) ≤
      380160 ∧
    Nat.card (Subgroup.centralizer {suzInv 3} ⊓ suzT : Subgroup (Equiv.Perm (Fin 1782))) ≤
      2419200 :=
  ⟨fun _ hg x y => suzT_adj hg x y, invGraph_regular, card_invCent_le (i := 0) (by norm_num),
    card_invCent_le (i := 1) (by norm_num), card_invCent_le (i := 2) (by norm_num),
    card_invCent_le (i := 3) (by norm_num), card_centralizer_le (i := 0) (by norm_num),
    card_centralizer_le (i := 1) (by norm_num), card_centralizer_le (i := 2) (by norm_num),
    card_centralizer_le (i := 3) (by norm_num)⟩

end CFSG.Sporadic.SuzOddCore
