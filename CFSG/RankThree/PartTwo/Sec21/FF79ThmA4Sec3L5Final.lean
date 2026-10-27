module

public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3L5Main
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L5KHolds

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.H4

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (KProper InCatalog)

variable {G : Type} [Group G] [Finite G]
variable {b : G} {J B A P D : Subgroup G}

theorem ff79_3_5_of_in_holds
    (hO : FF79KLemmaOP) (hG : IsSimpleGroup G) (hna : ∃ x y : G, x * y ≠ y * x)
    (hKp : KProper InCatalog G) (hs : FF79Sec3 b J) (h : FF79Sec34In4 b J B A P D) :
    FF79Concl35 b A :=
  ff79_3_5_of_in ff79KL35a_holds ff79KL35b_holds hO hG hna hKp hs h

end CFSG.RankThree.PartTwo.Sec21.FF79.H4
