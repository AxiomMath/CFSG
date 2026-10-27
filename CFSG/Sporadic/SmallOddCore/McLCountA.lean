module

public import CFSG.Sporadic.SmallOddCore.McLWords
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.SmallOddCore.McLWords
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
public import Certificates.Certificate2285

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

theorem mcl_wCountA :
    countPair PairMcL.bs 5 PairMcL.wA mclWConds PairMcL.blocks = 80640 :=
  Certificates.certificate2285

end CFSG.Sporadic.SmallOddCore
