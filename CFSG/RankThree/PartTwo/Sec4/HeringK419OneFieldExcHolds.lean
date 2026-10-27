module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldE9Types

public section

namespace CFSG.RankThree.PartTwo.Sec4

section Certs


theorem k419OneFieldG2_holds : K419OneFieldG2 :=
  k419OneFieldG2_of_E9 k419HasE9

theorem k419OneFieldTriality_holds :
    K419OneFieldTriality :=
  k419OneFieldTriality_of_E9 k419HasE9

theorem k419OneFieldLargeRee_holds : K419OneFieldLargeRee :=
  k419OneFieldLargeRee_of_E9 k419HasE9

end Certs

end CFSG.RankThree.PartTwo.Sec4
