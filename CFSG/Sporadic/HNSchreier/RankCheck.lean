module

public import CFSG.Sporadic.HNSchreier.InvolCheck
public import CFSG.Sporadic.HNSchreier.RankData
public import CFSG.Sporadic.HNSchreier.FAData
public meta import CFSG.Sporadic.HNSchreier.InvolCheck
public meta import CFSG.Sporadic.HNSchreier.RankData
public meta import CFSG.Sporadic.HNSchreier.FAData
public import CFSG.Sporadic.HNSchreier.RankCheckInputs
public import Certificates.Certificate2105

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.Sporadic.He.Native CFSG.ONSchreier.Native

theorem rank_cert : rankChecks rowsA rowsB rankCertRows = true :=
  Certificates.certificate2105

end CFSG.Sporadic.HNSchreier.Native
