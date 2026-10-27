module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.CoverAmb
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Detection
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Multiplier

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Blueprint (LieModel)
open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328Exc (AmbLeaves K328ExcLieModel)

theorem properComponent_cases {K : Type} [Group K] (h : K328ProperComponentLieModel K) :
    (LieModel K .PSL 4 2 2 ∨ LieModel K .PSp 3 2 2 ∨ LieModel K .POmegaMinus 4 2 2 ∨
      LieModel K .PSL 6 2 1 ∨ LieModel K .PSL 7 2 1 ∨ LieModel K .PSU 4 2 3 ∨
      LieModel K .PSp 3 2 3 ∨ LieModel K .POmegaMinus 4 2 3) ∨ K328ExcLieModel K := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · left; left; exact h
  · left; right; left; exact h
  · left; right; right; left; exact h
  · left; right; right; right; left; exact h
  · left; right; right; right; right; left; exact h
  · right; left; exact h
  · right; right; left; exact h
  · left; right; right; right; right; right; left; exact h
  · left; right; right; right; right; right; right; left; exact h
  · left; right; right; right; right; right; right; right; exact h
  · right; right; right; left; exact h
  · right; right; right; right; left; exact h
  · right; right; right; right; right; exact h

theorem mulEquiv_quotient_center_of_card_eq_one {K : Type} [Group K]
    (h : Nat.card (Subgroup.center K) = 1) : Nonempty (K ≃* (K ⧸ Subgroup.center K)) := by
  have hbot : Subgroup.center K = ⊥ := Subgroup.card_eq_one.1 h
  exact ⟨(QuotientGroup.quotientBot (G := K)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hbot.symm)⟩

theorem rowLeaves_or_ambLeaves_of_properComponent
    (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (h : K328ProperComponentLieModel (K ⧸ Subgroup.center K)) :
    RowLeaves K ∨ AmbLeaves K := by
  rcases properComponent_cases h with h | h
  · left
    obtain ⟨e⟩ := mulEquiv_quotient_center_of_card_eq_one (card_center_eq_one_of_classical hGA hq h)
    exact rowLeaves_of_mulEquiv e (classicalRows_holds _ h)
  · right
    exact ambLeaves_of_central_quotient hq.1
      (not_three_dvd_of_card_dvd_two (card_center_dvd_two_of_exceptional hGA hq h))
      (K328Exc.ambLeaves_of_k328ExcLieModel h)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
