module

public import CFSG.Sporadic.Co2Schreier.WitCheck
public import CFSG.Sporadic.Co2Schreier.ChainCheck
public import CFSG.Sporadic.Co2Schreier.Lin
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.ChainCheck
public meta import CFSG.Sporadic.Co2Schreier.Lin
public import CFSG.Sporadic.Co2Schreier.SixCheckInputs
public import Certificates.Certificate2057

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Co2Cert
  CFSG.Monster.B.Mathieu

theorem six_check : sixCheck witRec = true :=
  Certificates.certificate2057.1

theorem six_rows_eq :
    witRec.wLocal.sixRows = [[59, 52, 53, 56, 22, 16], [4, 15, 28, 21, 16, 50]] :=
  Certificates.certificate2057.2.1

theorem six_basis_eq :
    witRec.wLocal.sixBasisIndices = [516, 1588, 1809, 1630, 312, 1801] ∧
      witRec.wLocal.sixAnchor = 29 ∧ witRec.wLocal.sixGramRows = [54, 21, 59, 52, 47, 29] :=
  Certificates.certificate2057.2.2

end CFSG.Sporadic.Co2Schreier
