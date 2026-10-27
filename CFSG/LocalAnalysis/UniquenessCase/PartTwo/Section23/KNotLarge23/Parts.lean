module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNotLarge23.Orders
import CFSG.Adapters.StatedPSLTwo
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.Walter.J1Props.Elt
public import CFSG.Walter.Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem card_isL2 {X : Type} [Group X] {a : ℕ} (h : IsL2 X a) :
    1 ≤ a ∧ Nat.card X = 2 ^ a * ((2 ^ a) ^ 2 - 1) := by
  have hsc := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  exact ⟨hsc.1.2.1, StatedAPI.card_of_statedClassicalModel_psl_two_two hsc⟩

theorem card_isL2Odd {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsL2Odd X p) : Nat.card X * 2 = p * (p ^ 2 - 1) := by
  have hsc := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  simpa using StatedAPI.card_mul_two_of_statedClassicalModel_psl_two_odd hp hp2 hsc

theorem knl_l2 {Q : Type} [Group Q] [Finite Q] {a : ℕ} (hQ : IsL2 Q a)
    (N : Subgroup Q) [N.Normal] {n : ℕ} (hn : 3 ≤ n) :
    ¬ (IsSLn (Q ⧸ N) 3 n ∨ IsSp4 (Q ⧸ N) n ∨ IsU4 (Q ⧸ N) n) := by
  intro hT
  have hord := card_target (by omega) hT
  obtain ⟨ha, hQcard⟩ := card_isL2 hQ
  have hsimple : IsSimpleGroup Q := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hQ
  have hpos := knl_one_lt_order (by omega) hord
  rcases hsimple.eq_bot_or_eq_top_of_normal N with hN | hN
  · apply knl_ne_l2_order (by omega) ha hord
    rw [card_quotient_eq_index, hN, Subgroup.index_bot, hQcard]
  · rw [card_quotient_eq_index, hN, Subgroup.index_top] at hpos
    omega

theorem knl_l2odd {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : IsL2Odd Q p) (N : Subgroup Q) [N.Normal] {n : ℕ} (hn : 3 ≤ n) :
    ¬ (IsSLn (Q ⧸ N) 3 n ∨ IsSp4 (Q ⧸ N) n ∨ IsU4 (Q ⧸ N) n) := by
  intro hT
  have hord := card_target (by omega) hT
  have hQcard := card_isL2Odd hp hp2 hQ
  have hsimple : IsSimpleGroup Q := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hQ
  have hpos := knl_one_lt_order (by omega) hord
  rcases hsimple.eq_bot_or_eq_top_of_normal N with hN | hN
  · apply knl_ne_l2odd_order hn hp hp2 hord
    rw [card_quotient_eq_index, hN, Subgroup.index_bot, hQcard]
  · rw [card_quotient_eq_index, hN, Subgroup.index_top] at hpos
    omega

theorem card_isJ1 {X : Type} [Group X] (h : IsJ1 X) : Nat.card X = 175560 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card CFSG.Blueprint.NativeSporadic.J1 = 175560
  rw [← Nat.card_congr CFSG.Walter.walterJ1EquivNative.toEquiv]
  exact CFSG.Walter.J1Props.card_walterJ1

theorem knl_j1 {Q : Type} [Group Q] [Finite Q] (hQ : IsJ1 Q)
    (N : Subgroup Q) [N.Normal] {n : ℕ} (hn : 3 ≤ n) :
    ¬ (IsSLn (Q ⧸ N) 3 n ∨ IsSp4 (Q ⧸ N) n ∨ IsU4 (Q ⧸ N) n) := by
  intro hT
  have hord := card_target (by omega) hT
  have hdvd : Nat.card (Q ⧸ N) ∣ 175560 := by
    rw [card_quotient_eq_index, ← card_isJ1 hQ]
    exact Subgroup.index_dvd_card N
  exact knl_not_dvd_j1 hn hord hdvd

theorem knl_square {X : Type} [Group X] {n : ℕ} (hn : 3 ≤ n) (hX : IsL2Square X n) :
    ¬ (IsSLn X 3 n ∨ IsSp4 X n ∨ IsU4 X n) := by
  intro hT
  have hord := card_target (by omega) hT
  obtain ⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩ := hX
  have hAc := (card_isL2 hA).2
  have hBc := (card_isL2 hB).2
  apply knl_ne_square_order (by omega) hord
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, hAc, hBc]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23

end
