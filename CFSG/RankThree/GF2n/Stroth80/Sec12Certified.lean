module

public import CFSG.RankThree.GF2n.Stroth80.Sec12GenByB
public import CFSG.RankThree.GF2n.Stroth80.Sec37Certified

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Certs

theorem strothGenByBStatement_certified : StrothGenByBStatement :=
  strothGenByB_of_T75 timmesfeldTransitivityTI_holds

end Certs

end CFSG.RankThree.GF2n.Stroth80
