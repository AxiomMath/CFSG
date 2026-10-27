module

public import CFSG.RankThree.PartOne.MB3.Final
public import CFSG.RankThree.PartOne.MB3.Seven

public section

namespace CFSG.RankThree.PartOne.MB3

open CFSG CFSG.Assembly CFSG.RankThree CFSG.LocalAnalysis.ComponentInitial

open CFSG.Blueprint in
theorem maximalBranchThree_holds (hS : SchreierFor InCatalog)
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (h68 : Sec6EightMultipliers) (hCVD : CoreVanishingDichotomy)
    (hSmall : SevenSmallPrimeCase) : MaximalBranchThree :=
  maximalBranchThree_of hS hbridge h68 (movingQuasisimpleSeven_of hCVD hSmall)

end CFSG.RankThree.PartOne.MB3
