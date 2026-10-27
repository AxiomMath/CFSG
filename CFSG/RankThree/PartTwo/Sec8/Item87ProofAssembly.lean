module

public import CFSG.RankThree.PartTwo.Sec8.Item87Proof88

public section

namespace CFSG.RankThree.PartTwo.Sec8

theorem item88_of_steps (h418 : Item418Theta) (hF : KF84Field) (hI : KF88Inner) : Item88 :=
  item88_of h418 (pair84A_of h418 hF) hF hI

theorem item88_of_step (h48 : Sec4.Item4_8) (h418 : Item418Theta) (hF : KF84Field)
    (hS : KF88Step) : Item88 :=
  item88_of_steps h418 hF (kF88Inner_of h48 hS)

end CFSG.RankThree.PartTwo.Sec8
