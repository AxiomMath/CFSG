module

public import CFSG.RankThree.PartOne.F106.ResidualsFour
public import CFSG.RankThree.PartOne.F106.NcMain

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.RankThree.PartOne.N143 (SectionListBound)

structure FourResidualsK : Prop where
  atThree : NoQD32AtThree
  f4 : NoQD32F4
  nonabelian : NoQD32NonabelianRest
  kfact : KFactFive

theorem fourResiduals_of_k (hS : SchreierFor InCatalog) (hTwo : TwoActionInputs)
    (hI : InSec10Seven) (hSLB : SectionListBound) (hR : FourResidualsK) : FourResiduals :=
  ⟨hR.atThree, hR.f4, hR.nonabelian,
    fiveNoncentralExcluded_of_kFactFive hS hTwo hI hSLB hR.kfact⟩

theorem fiveInputs_of_four_residuals_k
    (hS : SchreierFor InCatalog) (hTwo : TwoActionInputs) (hI : InSec10Seven)
    (hSLB : SectionListBound) (hR : FourResidualsK) : FiveInputs :=
  fiveInputs_of_four_residuals (fourResiduals_of_k hS hTwo hI hSLB hR)

end CFSG.RankThree.PartOne.F106
