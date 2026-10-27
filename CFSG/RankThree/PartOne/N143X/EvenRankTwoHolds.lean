module

public import CFSG.RankThree.PartOne.N143X.EvenRankTwo
public import CFSG.RankThree.PartOne.N143X.TrialityRank
public import CFSG.RankThree.PartOne.N143X.ReeRank

public section

namespace CFSG.RankThree.PartOne.N143X

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem evenRankTwoExceptionalNoPCube_holds :
    EvenRankTwoExceptionalNoPCube := by
  intro X _ _ f hX p hp hp7 E hE hcard
  have hpow : ∀ x ∈ E, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  rcases hX with hX | hX
  · exact false_of_pow_three_triality hX hp hp7 hpow hcard
  · exact false_of_pow_three_ree hX hp hp7 hpow hcard

end CFSG.RankThree.PartOne.N143X
