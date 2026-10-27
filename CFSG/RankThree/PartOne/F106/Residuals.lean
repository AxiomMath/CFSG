module

public import CFSG.RankThree.PartOne.F106.Bundle
public import CFSG.RankThree.PartOne.F106.NoQD32

public section

namespace CFSG.RankThree.PartOne.F106

structure FiveResiduals : Prop where
  converse : EvenListConverse
  atThree : NoQD32AtThree
  f4 : NoQD32F4
  nonabelian : NoQD32NonabelianRest
  noncentral : FiveNoncentralExcluded

theorem fiveInputs_of_residuals_of
    (hU6 : U6ThreeRank) (hF4 : F4ThreeRank) (hR : FiveResiduals) : FiveInputs :=
  ⟨evenLieFiveRank_of_converse hR.converse hU6 hF4,
    evenLieNoQD32_of_converse hR.converse hR.atThree hR.f4 hR.nonabelian, hR.noncentral⟩

end CFSG.RankThree.PartOne.F106
