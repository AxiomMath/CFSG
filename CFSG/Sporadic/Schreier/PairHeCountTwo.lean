
module

public import CFSG.Sporadic.Schreier.PairHeCountTwoBase
import all CFSG.Sporadic.Schreier.PairHeCountTwoBase

public import CFSG.Sporadic.Schreier.PairHeCheck
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.Schreier.PairHeCheck
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.CertPChainData
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
public import Certificates.Certificate2224

public section

namespace CFSG.Sporadic.Schreier.PairHe

open CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB

theorem count_two : countOrd bs 2 heBlocks = 212415 :=
  Certificates.certificate2224

end CFSG.Sporadic.Schreier.PairHe
