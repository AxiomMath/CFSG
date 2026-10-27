
module

public import CFSG.Sporadic.Schreier.J4SRankCheckBase

public import CFSG.Sporadic.Schreier.J4SRankData
public meta import CFSG.Sporadic.Schreier.J4SRankData
public import Certificates.Certificate2180

public section

namespace CFSG.Sporadic.J4Schreier

theorem rows3_eta : rows3OK (etaP 1).1 = true ∧ rows3OK (etaP 14).1 = true :=
  Certificates.certificate2180.1

theorem q3Rows_eq : q3RowsOK Q3GenPairs = true :=
  Certificates.certificate2180.2

end CFSG.Sporadic.J4Schreier
