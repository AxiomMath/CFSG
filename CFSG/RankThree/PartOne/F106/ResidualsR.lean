module

public import CFSG.RankThree.PartOne.F106.ResidualsK
public import CFSG.RankThree.PartOne.F106.OddRad

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.RankThree.PartOne.N143 (SectionListBound)

structure FourResidualsR : Prop where
  atThree : NoQD32AtThree
  f4 : NoQD32F4
  nonabelian : NoQD32NonabelianRest
  oddRad : OddRadFive

theorem fourResidualsK_of_r (hR : FourResidualsR) : FourResidualsK :=
  ⟨hR.atThree, hR.f4, hR.nonabelian, kFactFive_of_oddRadFive hR.oddRad⟩

theorem fiveInputs_of_four_residuals_r
    (hS : SchreierFor InCatalog) (hTwo : TwoActionInputs) (hI : InSec10Seven)
    (hSLB : SectionListBound) (hR : FourResidualsR) : FiveInputs :=
  fiveInputs_of_four_residuals_k hS hTwo hI hSLB (fourResidualsK_of_r hR)

end CFSG.RankThree.PartOne.F106
