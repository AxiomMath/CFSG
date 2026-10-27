module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res3ProofS7
public import CFSG.RankThree.PartTwo.Sec21.Item211Res3ProofON
public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofM12

public section

namespace CFSG.RankThree.PartTwo.Sec21

section Certs

theorem item211ResidualSmall_of_res3
    (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (h14 : Sec4.Item4_14) : Item211ResidualSmall :=
  item211ResidualSmall_of_item414 h45 h66 h14 ks211TwoLocalS7 (item211ResidualON_of h45 h66)

end Certs

end CFSG.RankThree.PartTwo.Sec21
