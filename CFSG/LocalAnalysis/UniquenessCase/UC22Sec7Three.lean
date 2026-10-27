module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
import CFSG.LocalAnalysis.UniquenessCase.UC22SigmaThreeStrong
import CFSG.LocalAnalysis.UniquenessCase.UC7P3NoBad
import CFSG.LocalAnalysis.UniquenessCase.UC7P3Theorem76

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem c76ThreeN1_of_stronglyEmbeddedThree (hK : StronglyEmbeddedThree) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) : C76ThreeN1 S := by
  intro hσ h3 hsp
  exact Sec7Core4.conclusion76_of_stronglyEmbeddedThree
    (.ofUnique hS hU S.M S.maxLocal 3
      (UC22.three_mem_uniqueFourSigma_of_mem_uniqueFourBeta S hσ h3) hsp) rfl hK

theorem c76ThreeN2_of_inputs (hSE : StronglyEmbeddedFive) (hB : BadNoStrongThree)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) : C76ThreeN2 S := by
  intro hσ h3 p hp hp5 hsp
  let k : Sec7Core4 G := .ofUnique hS hU S.M S.maxLocal p hp hsp
  exact k.conclusion76_of_kIDExcluded hp5
    (k.kIDExcluded_of_strongThree hp5
      (UC22.isStronglyPEmbedded_three_of_mem_uniqueFourBeta hU S hσ h3) hB) hSE

theorem c76Three_of_inputs (hSE : StronglyEmbeddedFive) (hK : StronglyEmbeddedThree)
    (hB : BadNoStrongThree) (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) :
    C76Three S :=
  C76Three_of_N1_N2 S (c76ThreeN1_of_stronglyEmbeddedThree hK hS hU S)
    (c76ThreeN2_of_inputs hSE hB hS hU S)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
