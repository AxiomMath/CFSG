module

public import CFSG.Sporadic.FischerOddCore.Fi22CentCheck
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
public import CFSG.Monster.B.Fischer.Fi22GraphBoundCheck
public import Certificates.Data.CFSGNative.FischerOddCore.Checks
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
public meta import CFSG.Monster.B.Fischer.Fi22GraphBoundCheck
public meta import Certificates.Data.CFSGNative.FischerOddCore.Checks

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore.Native

@[expose] def fi22RelBoundOK (c : Nat) : Bool :=
  boundsOK 3510 fi22Nbr (fi22ExtArr (21 + fi22CentCases.getD c 0))
    (fi22CentRefPoints.getD (c - 1) []) (fi22CentRefBounds.getD (c - 1) []) 4

end CFSG.Sporadic.FischerOddCore
