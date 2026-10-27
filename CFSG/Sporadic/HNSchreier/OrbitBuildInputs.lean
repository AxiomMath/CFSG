module

public import Certificates.Data.CFSGNative.HN.Data
public import CFSG.Sporadic.HNSchreier.Data
public meta import Certificates.Data.CFSGNative.HN.Data
public meta import CFSG.Sporadic.HNSchreier.Data
public meta import Mathlib.Init
public import Mathlib.Init

public section
namespace CFSG.Sporadic.HNSchreier.Native

@[expose] def hnsBFSData : CFSG.Sporadic.F5.Native.F5Data :=
  { CFSG.Sporadic.HN.Native.hnData with root := Data.rootDigits, Q := Data.checkPts }

end CFSG.Sporadic.HNSchreier.Native
