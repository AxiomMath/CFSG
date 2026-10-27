module

public import CFSG.RankThree.PartOne.F106.ConvAll
public import CFSG.RankThree.PartOne.F106.Residuals
public import CFSG.RankThree.PartOne.F106.ThreeRankHolds

public section

namespace CFSG.RankThree.PartOne.F106

structure FourResiduals : Prop where
  atThree : NoQD32AtThree
  f4 : NoQD32F4
  nonabelian : NoQD32NonabelianRest
  noncentral : FiveNoncentralExcluded

theorem fiveInputs_of_four_residuals
    (hR : FourResiduals) : FiveInputs :=
  fiveInputs_of_residuals_of u6ThreeRank_holds f4ThreeRank_holds
      ⟨evenListConverse_of, hR.atThree, hR.f4, hR.nonabelian, hR.noncentral⟩

end CFSG.RankThree.PartOne.F106
