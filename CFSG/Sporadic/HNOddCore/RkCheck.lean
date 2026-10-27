module

public import CFSG.Sporadic.HNSchreier.RankCheck
public import CFSG.Sporadic.HNOddCore.RankData
public import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.RankCheck
public meta import CFSG.Sporadic.HNOddCore.RankData
public meta import CFSG.Sporadic.HNOddCore.InvData
public import CFSG.Sporadic.HNOddCore.RkCheckInputs
public import Certificates.Certificate2090

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.Sporadic.He.Native CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier
open CFSG.Sporadic.HNSchreier.Native

@[expose] def invRanks : List Nat := [56, 64, 56]

theorem inv_rank_cert : invRankChecks rowsA rowsB invRankRows = true :=
  Certificates.certificate2090

end CFSG.Sporadic.HNOddCore.Native
