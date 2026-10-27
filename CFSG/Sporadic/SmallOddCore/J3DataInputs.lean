module

public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Sporadic.Schreier.PairJ3Cert
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public meta import CFSG.Sporadic.SmallOddCore.CentData

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier

@[expose] def j3CentHex : String := include_str "J3Cent.txt"

@[expose] def j3CentTbl (k : ℕ) : Table := hexT 4 6156 (6156 * k) j3CentHex

end CFSG.Sporadic.SmallOddCore
