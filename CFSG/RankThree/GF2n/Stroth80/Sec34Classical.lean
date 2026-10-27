module

public import CFSG.RankThree.GF2n.Stroth80.Sec34CaseB
public import CFSG.RankThree.GF2n.Stroth80.Sec37Certified

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Certs

theorem stroth34Statement_of_classical (hHKS : HKSStatement) (hSL2 : SL2ModuleDimStatement) :
    Stroth34Statement :=
  stroth34Statement_certified hHKS hSL2 stroth34CaseB

theorem stroth37Statement_of_classical (hHKS : HKSNormalStatement) (hSL2 : SL2ModuleDimStatement)
    (hSLfix : SL2FixedLineDimStatement) : Stroth37Statement :=
  stroth37Statement_certified hHKS hSL2 hSLfix stroth34CaseB

end Certs

end CFSG.RankThree.GF2n.Stroth80
