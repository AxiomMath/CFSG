module

public import CFSG.CGT.A8S.Final
public import CFSG.CGT.M24S.Main
public import CFSG.LargeExtraspecial.TI75Bridge
public import CFSG.LargeExtraspecial.TI75Form2
public import CFSG.RankThree.GF2n.Stroth80.Sec37Final

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Certs

theorem form2StrongStmt_holds : CFSG.LargeExtraspecial.S4.Form2StrongStmt :=
  CFSG.LargeExtraspecial.TI75.form2StrongStmt_of_inputs
    (CFSG.LargeExtraspecial.TI75Bridge.simpleCaseStmt_of_rest
      ⟨CFSG.CGT.A8S.a8SylowInput, CFSG.CGT.M24S.m24SylowInput⟩)
    CFSG.CGT.Timmesfeld75.lemma215
    CFSG.CGT.Timmesfeld75.listWCIdentification_of_cert

theorem timmesfeldTransitivityTI_holds :
    CFSG.CGT.Timmesfeld75.TimmesfeldTransitivityTI :=
  CFSG.CGT.Timmesfeld75.timmesfeldTransitivityTI_of_inputs
    (CFSG.LargeExtraspecial.TI75Bridge.simpleCaseStmt_of_rest
      ⟨CFSG.CGT.A8S.a8SylowInput, CFSG.CGT.M24S.m24SylowInput⟩)
    CFSG.CGT.Timmesfeld75.lemma215

theorem stroth34Statement_certified (hHKS : HKSStatement) (hSL2 : SL2ModuleDimStatement)
    (hB : Stroth34CaseBStatement) : Stroth34Statement :=
  stroth34Statement_of_inputs timmesfeldTransitivityTI_holds hHKS hSL2 hB

theorem stroth37Statement_certified (hHKS : HKSNormalStatement) (hSL2 : SL2ModuleDimStatement)
    (hSLfix : SL2FixedLineDimStatement) (hB : Stroth34CaseBStatement) : Stroth37Statement :=
  stroth37Statement_of_classical_inputs timmesfeldTransitivityTI_holds form2StrongStmt_holds
    hHKS hSL2 hSLfix hB

end Certs

end CFSG.RankThree.GF2n.Stroth80
