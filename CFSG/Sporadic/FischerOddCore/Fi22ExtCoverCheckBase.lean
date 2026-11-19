
module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckBase
public import Certificates.Data.CFSGNative.FischerOddCore.Checks
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckBase
public meta import Certificates.Data.CFSGNative.FischerOddCore.Checks
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverCheckInputs

@[expose] public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore.Native

def fi22ExtResArr (I : Nat) : Array Nat :=
  resIdx 256 fi22TLevels fi22ExtQArr fi22ExtQiArr fi22ExtVArr fi22ExtDArr fi22ExtPosArr I

end CFSG.Sporadic.FischerOddCore
