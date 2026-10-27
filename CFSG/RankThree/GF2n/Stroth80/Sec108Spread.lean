module

public import CFSG.RankThree.GF2n.Stroth80.Sec108Main
public import CFSG.StandardComponent.AschbacherSeitz.Main
public import CFSG.RankThree.GF2n.Tim79a34HJRepresentation
public import CFSG.RankThree.GF2n.Stroth80.Sec101Proved
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVISpread

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81

section Certs

theorem stroth108CoreStatement_of_spread (hspread : StrothNoA2SpreadStatement) :
    Stroth108CoreStatement :=
  stroth108Core_of_inputs stroth34Statement_unconditional stroth311aStatement_unconditional
    hspread Tim79a.aschbacherSeitzStatement_holds
    ComponentClassification.Asc76X.goldschmidtTheoremA
    (fun _ _ _ _ h =>
      ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC.outCyc_of_goldschmidtSimpleType h)
    Tim79a.aschbacherHJRepresentationStatement_holds
    ComponentClassification.RankTwoClassical.m12AutThreeFive

theorem stroth108Statement_of_h1111 (h1111 : Stroth1111Statement) : Stroth108Statement :=
  stroth108Statement_of_spread (strothNoA2Spread_of_h1111 h1111)
    (stroth108CoreStatement_of_spread (strothNoA2Spread_of_h1111 h1111))

end Certs

end CFSG.RankThree.GF2n.Stroth80
