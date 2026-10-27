
module

public import CFSG.Sporadic.HNSchreier.ThreeCheckBase

public import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNSchreier.FAData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public meta import CFSG.Sporadic.HNSchreier.FAData
public import CFSG.Sporadic.HNSchreier.ThreeCheckInputs
public import Certificates.Certificate2109

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.F5.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native

theorem three_cert : threeChecks (hnsData.orbit ()) = true :=
  Certificates.certificate2109

end CFSG.Sporadic.HNSchreier.Native
