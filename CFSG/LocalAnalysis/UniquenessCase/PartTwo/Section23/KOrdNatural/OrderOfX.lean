module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
import CFSG.Timmesfeld.Orders.Classical
public import CFSG.ClassicalGroups.Orthogonal.Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.Timmesfeld.ClassicalOrders

theorem isL2_two_le_and_card {X : Type} [Group X] {n : ℕ} (h : IsL2 X n) :
    2 ≤ n ∧ Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have hadm : Nat.Prime 2 ∧ 1 ≤ n ∧ (2 ≤ 2 ∧ (2, 2 ^ n) ≠ (2, 2) ∧ (2, 2 ^ n) ≠ (2, 3)) :=
    CFSG.Blueprint.LieModel.admissible h
  obtain ⟨-, h1, -, hne, -⟩ := hadm
  have hn1 : n ≠ 1 := fun hn => hne (by simp [hn])
  have hscm : StatedClassicalModel X .PSL 2 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel (t := .PSL) h (by decide)
  exact ⟨by omega, CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hscm⟩

theorem isOmegaMinus_four_one_le_and_card {X : Type} [Group X] {n : ℕ} (h : IsOmegaMinus X 4 n) :
    1 ≤ n ∧ Nat.card X = (2 ^ n) ^ 2 * ((2 ^ n) ^ 4 - 1) := by
  obtain ⟨-, K, hKf, hKfin, b, c, hKcard, hirr, hR⟩ := h
  change Nonempty (X ≃* StatedProj (StatedOmega (StatedQuadMinus 2 K b c))) at hR
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  obtain ⟨e⟩ := hR
  have hn : 1 ≤ n := by
    by_contra hlt
    have hn0 : n = 0 := Nat.lt_one_iff.mp (not_le.mp hlt)
    rw [hn0, pow_zero] at hKcard
    have h2 := Finite.one_lt_card (α := K)
    omega
  refine ⟨hn, ?_⟩
  have hproj : Nat.card (StatedProj (StatedOmega (StatedQuadMinus 2 K b c))) =
      Nat.card (StatedOmega (StatedQuadMinus 2 K b c)) := by
    let P : HypPair (quadMinus 2 K b c) := minusPair K b c (⟨0, by norm_num⟩ : Fin 1)
    refine CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega
      (Q := quadMinus 2 K b c) (Q₀ := StatedQuadMinus 2 K b c)
      (coe_quadMinus 2 K b c) ?_
    exact ⟨P.e + P.f, by rw [map_add_eq_one_of_hypPair P]; exact one_ne_zero⟩
  have hexp : ((2 ^ n) ^ 2) ^ 2 = (2 ^ n) ^ 4 := by ring
  rw [Nat.card_congr e.toEquiv, hproj,
    CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_two hirr,
    CFSG.SeitzReduction.F4Pilot.ordSL_two, hKcard, hexp]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

end
