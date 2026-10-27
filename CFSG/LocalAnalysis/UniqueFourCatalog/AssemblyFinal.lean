module

public import CFSG.LocalAnalysis.UniqueFourCatalog.Assembly
public import CFSG.LocalAnalysis.UniqueFourCatalog.TwistedE6OddExclusion
public import CFSG.LocalAnalysis.UniqueFourCatalog.TrialityD4Odd
public import CFSG.LocalAnalysis.UniqueFourCatalog.OddExceptionalUntwisted

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

section Final

set_option linter.unusedSectionVars false


theorem untwistedExceptionalOddExclusion
    : UntwistedExceptionalOddExclusion :=
  fun _ _ _ hS _ ht _ _ hp2 h => false_of_untwistedExceptional_odd hS ht hp2 h

theorem catalogNoUniqueFour
    : CFSG.Yardstones.Mf4cdcdf2e013.CatalogNoUniqueFour :=
  catalogNoUniqueFour_of_oddExceptional twistedE6OddExclusion trialityD4OddExclusion
    untwistedExceptionalOddExclusion

end Final

end CFSG.LocalAnalysis.UniqueFourCatalog
