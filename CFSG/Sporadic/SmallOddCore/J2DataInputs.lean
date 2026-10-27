module

public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Sporadic.Schreier.PairJ2Cert
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public meta import CFSG.Sporadic.SmallOddCore.CentData

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier

@[expose] def j2CentHex : String := include_str "J2Cent.txt"

@[expose] def j2CentTbl (k : ℕ) : Table := hexT 3 315 (315 * k) j2CentHex

end CFSG.Sporadic.SmallOddCore
