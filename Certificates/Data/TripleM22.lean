module

public import Certificates.Data.CFSGNative.HS.Cert
public import CFSG.CGT.T75JM.M22PresInputs
public import CFSG.Sporadic.HS.Group

public section

namespace CFSG.Sporadic.Mathieu.Native

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallF2.Native

@[expose] def tA : String := include_str "TripleM22A.m1"

@[expose] def tB : String := include_str "TripleM22B.m1"

end CFSG.Sporadic.Mathieu.Native
