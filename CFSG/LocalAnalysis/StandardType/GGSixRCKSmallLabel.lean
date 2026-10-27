module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKSmallOrders
public import CFSG.LocalAnalysis.StandardType.MarkingDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynOrders
import CFSG.LocalAnalysis.GLTheoremA.CatA.MILabel

public section

namespace CFSG.StandardType.RCKSmall

open CFSG.Open

theorem tag_ne_of_notSmall
    {X : Type} [Group X] {lab : CFSG.Assembly.LargeEvenLabel}
    (hX : ∃ t r e, ¬ RCKSmallLieTag t ∧ CFSG.Blueprint.LieModel X t r 2 e)
    (hl : CFSG.Assembly.LargeEvenInLambda2 lab) (hM : MarkedModel lab X) :
    lab.tag ≠ .G2 ∧ lab.tag ≠ .B2der ∧ lab.tag ≠ .G2der ∧ lab.tag ≠ .twF4der ∧
      lab.tag ≠ .twB2 ∧ lab.tag ≠ .twF4 := by
  obtain ⟨t, r, e, hns, hLM⟩ := hX
  obtain ⟨lt, ll, ln⟩ := lab
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    exact false_of_lieModel_small hLM hns
      (by simpa only [MarkedModel, markTag, markRank, markChar, markDeg] using hM) (Or.inl rfl)
  · rintro rfl
    have h360 : Nat.card X = 360 := ggMarkedModel_card_b2der rfl hM
    have hne : CFSG.SeitzReduction.F4Pilot.evenLieOrder t r e ≠ 360 :=
      ClNonsplit.evenLieOrder_ne_three_sixty_of_admissible hLM.admissible
    rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hLM] at h360
    exact hne h360
  · rintro rfl
    exact CFSG.LocalAnalysis.GLTheoremA.I141F.Ord.card_ne_6048_of_lieModel hLM
      (CFSG.LocalAnalysis.GLTheoremA.MI.card_markedModel_g2der rfl hM)
  · rintro rfl
    exact false_of_lieModel_small hLM hns
      (by simpa only [MarkedModel, markTag, markRank, markChar, markDeg] using hM)
      (Or.inr (Or.inr (Or.inr rfl)))
  · rintro rfl
    exact false_of_lieModel_small hLM hns
      (by simpa only [MarkedModel, markTag, markRank, markChar, markDeg] using hM)
      (Or.inr (Or.inl rfl))
  · rintro rfl
    exact false_of_lieModel_small hLM hns
      (by simpa only [MarkedModel, markTag, markRank, markChar, markDeg] using hM)
      (Or.inr (Or.inr (Or.inl rfl)))

end CFSG.StandardType.RCKSmall
