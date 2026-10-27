module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Theorem76
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Bad
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Setup4Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

variable {G : Type} [Group G] [Finite G]

theorem r76_dataOfSetup4 (hSE : PartOne.Section7.StronglyEmbeddedFive)
    (hSE3 : PartOne.Section7.StronglyEmbeddedThree) (hB : PartOne.Section7.BadNoStrongThree)
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hPart : PartIAt S.M) : UC22.F07.R76 (dataOfSetup4 hS hU S) := by
  intro p hp hp2 hsp
  rcases eq_or_ne p 3 with rfl | hp3
  · exact (PartOne.Section7.R72.setup4Core hS hU S hPart 3 hp hp2
      hsp).conclusion76_of_stronglyEmbeddedThree rfl hSE3
  · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    let k := PartOne.Section7.R72.setup4Core hS hU S hPart p hp hp2 hsp
    exact k.conclusion76_of_kIDExcluded hp5
      (PartOne.Section7.R72.kIDExcluded_of_setup4 hU S hMS hB k rfl hp5) hSE

end CFSG.LocalAnalysis.UniquenessCase.UC6
