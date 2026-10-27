module

public import CFSG.Sporadic.SuzOddCore.GraphArrays
public import CFSG.Sporadic.SuzOddCore.ArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Refine
public meta import CFSG.Sporadic.SuzOddCore.GraphArrays
public meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Refine

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def matHeader (s : String) : List Nat := ((mtxTokens s).take 4).map tokenVal

@[expose] def matDigits (s : String) : List Char :=
  ((s.toList.dropWhile (· != '\n')).drop 1).filter fun c => !c.isWhitespace

end CFSG.Sporadic.SuzOddCore
