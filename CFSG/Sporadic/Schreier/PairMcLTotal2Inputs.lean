module

public import CFSG.Sporadic.Schreier.PairMcLCheck
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts

public section

namespace CFSG.Sporadic.Schreier.PairMcL

open CFSG.Sporadic.Schreier.PairNative

@[expose] def pat10 : List Bool := [false, true, false, true, true, false, true, true, true]

@[expose] def conds2 : List (List Bool × Nat) :=
  [([false, true], 11), (commPat, 5), ([false, true, true], 12),
    ([false, true, false, true, true], 14), (pat10, 10)]

end CFSG.Sporadic.Schreier.PairMcL
