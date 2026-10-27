
module

public import CFSG.Sporadic.Schreier.PairJ3CountBase

public import CFSG.Sporadic.Schreier.PairJ3Check
public import Certificates.Data.CFSGNative.PairSchreier.Preds
public meta import CFSG.Sporadic.Schreier.PairJ3Check
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Preds
public import Certificates.Certificate2238

public section

namespace CFSG.Sporadic.Schreier.PairJ3

open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem count_two : parCount (ordPred bs 2) blocks = 26163 :=
  Certificates.certificate2238.1

theorem count_three : parCount (ordPred bs 3) blocks = 253232 :=
  Certificates.certificate2238.2.1

theorem total :
    (cl.map fun c => c.2.1.size * parCount (pairPred bs 3 c.1 conds) blocks).sum =
      301397760 :=
  Certificates.certificate2238.2.2

end CFSG.Sporadic.Schreier.PairJ3
