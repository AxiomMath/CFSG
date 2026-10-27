module

public import CFSG.Sporadic.Schreier.PairMcLCheck
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
public import Certificates.Certificate2245

public section

namespace CFSG.Sporadic.Schreier.PairMcL

open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem total :
    (cl.map fun c => c.2.1.size * countPair bs 5 c.1 conds blocks).sum = 48498912000 :=
  Certificates.certificate2245

end CFSG.Sporadic.Schreier.PairMcL
