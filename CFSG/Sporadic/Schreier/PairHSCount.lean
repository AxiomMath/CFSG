
module

public import CFSG.Sporadic.Schreier.PairHSCountBase

public import CFSG.Sporadic.Schreier.PairHSCheck
public import Certificates.Data.CFSGNative.PairSchreier.Preds
public meta import CFSG.Sporadic.Schreier.PairHSCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Preds
public import Certificates.Certificate2220

public section

namespace CFSG.Sporadic.Schreier.PairHS

open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem count_two : parCount (ordPred bs 2) blocks = 21175 :=
  Certificates.certificate2220.1

theorem count_five : parCount (ordPred bs 5) blocks = 2010624 :=
  Certificates.certificate2220.2.1

theorem total :
    (cl.map fun c => c.2.1.size * parCount (pairPred bs 5 c.1 conds) blocks).sum =
      1064448000 :=
  Certificates.certificate2220.2.2

end CFSG.Sporadic.Schreier.PairHS
