module

public import CFSG.Sporadic.Schreier.PairMcLCheck
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
public import Certificates.Certificate2242

public section

namespace CFSG.Sporadic.Schreier.PairMcL

open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem count_five : countOrd bs 5 blocks = 37122624 :=
  Certificates.certificate2242

end CFSG.Sporadic.Schreier.PairMcL
