module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcTwE6
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAut

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

section Bundle


@[expose] def GGOrdPInnerExcRest : Prop :=
  GGOrdPToralF4Rest ∧ GGOrdPToralE6Rest ∧ GGOrdPToralE7Rest ∧ GGOrdPToralE8Rest ∧
    GGTwE6InndiagOrdPInnerInput ∧ GGTwE6CenterTrivialInput ∧ GGOrdPToralTwE6Input

theorem ggOrdPInnerConjExc_of_rest (h : GGOrdPInnerExcRest) :
    ∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
      t ≠ .POmegaMinus → GGOrdPInnerConjAt t := by
  obtain ⟨hF4, hE6, hE7, hE8, hI, hZ, hT⟩ := h
  intro t hs h1 h2 h3 h4 h5
  cases t with
  | F4 => exact ggOrdPInnerConjAt_F4_of_toral (ggOrdPToralUnivAt_F4_of_rest hF4)
  | E6 => exact ggOrdPInnerConjAt_E6_of_toral (ggOrdPToralUnivAt_E6_of_rest hE6)
  | E7 => exact ggOrdPInnerConjAt_E7_of_toral (ggOrdPToralUnivAt_E7_of_rest hE7)
  | E8 => exact ggOrdPInnerConjAt_E8_of_toral (ggOrdPToralUnivAt_E8_of_rest hE8)
  | twistedE6 => exact ggOrdPInnerConjAt_twistedE6_of_inputs hI hZ hT
  | PSL => exact (h1 rfl).elim
  | PSp => exact (h2 rfl).elim
  | PSU => exact (h3 rfl).elim
  | POmegaPlus => exact (h4 rfl).elim
  | POmegaMinus => exact (h5 rfl).elim
  | POmegaOdd | G2 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
    exact (hs (by simp [GGOrdPSmallTag])).elim

end Bundle

end CFSG.StandardType
