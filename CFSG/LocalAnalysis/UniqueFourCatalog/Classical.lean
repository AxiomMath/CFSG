module

public import CFSG.LocalAnalysis.UniqueFourCatalog.Linear
public import CFSG.LocalAnalysis.UniqueFourCatalog.Symplectic
public import CFSG.LocalAnalysis.UniqueFourCatalog.Orthogonal
public import CFSG.LocalAnalysis.UniqueFourCatalog.OddLinear
public import CFSG.LocalAnalysis.UniqueFourCatalog.OddUnitary
public import CFSG.LocalAnalysis.UniqueFourCatalog.OddSymplectic
public import CFSG.LocalAnalysis.UniqueFourCatalog.OddOrthogonal

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem not_uniqueFour_of_statedClassicalModel (hS : Standing4 G) {t : StatedLieTag}
    {n p f : ℕ} (h : StatedClassicalModel G t n p f) : ¬ uniqueFourUnique G := by
  by_cases hp : p = 2
  · subst hp
    cases t with
    | PSL => exact not_uniqueFour_of_statedPSL hS h
    | PSU => exact not_uniqueFour_of_statedPSU hS h
    | PSp => exact not_uniqueFour_of_statedPSp hS h
    | POmegaOdd => exact absurd rfl h.1.2.2.2
    | POmegaPlus => exact not_uniqueFour_of_statedPOmegaPlus hS h
    | POmegaMinus => exact not_uniqueFour_of_statedPOmegaMinus hS h
    | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
      exact h.2.elim
  · cases t with
    | PSL => exact fun _ => false_of_statedPSL_odd hS hp h
    | PSU => exact fun _ => false_of_statedPSU_odd hS hp h
    | PSp => exact not_uniqueFour_of_statedPSp_odd hS hp h
    | POmegaOdd => exact fun _ => false_of_statedPOmegaOdd hS h
    | POmegaPlus => exact fun _ => false_of_statedPOmegaPlus_odd hS hp h
    | POmegaMinus => exact fun _ => false_of_statedPOmegaMinus_odd hS hp h
    | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
      exact h.2.elim

end CFSG.LocalAnalysis.UniqueFourCatalog
