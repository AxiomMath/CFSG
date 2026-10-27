module

public import CFSG.RankThree.PartOne.F106.Five
public import CFSG.RankThree.PartOne.MB3.Seven

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.RankThree.PartOne.N143 (SectionListBound)

structure FiveInputs : Prop where
  rank : EvenLieFiveRank
  noQD32 : EvenLieNoQD32
  noncentral : FiveNoncentralExcluded

theorem full106_of_bundle (hCVD : CoreVanishingDichotomy) (hI : InSec10Seven)
    (hSLB : SectionListBound) (hSmall7 : MB3.SevenSmallPrimeCase) (hB : FiveInputs) :
    K156.Full106Stmt :=
  full106_of_inputs (MB3.movingQuasisimpleSeven_of hCVD hSmall7) hCVD hI hSLB hB.rank hB.noQD32
    hB.noncentral

end CFSG.RankThree.PartOne.F106
