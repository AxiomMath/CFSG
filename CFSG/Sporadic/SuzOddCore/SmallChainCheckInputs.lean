module

public import CFSG.Sporadic.SuzOddCore.ArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def smallLevels : Array Level := rawLevels 1782 smallStrongArrs smallBaseNat.toArray

end CFSG.Sporadic.SuzOddCore
