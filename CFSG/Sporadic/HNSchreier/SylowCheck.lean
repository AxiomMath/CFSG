
module

public import CFSG.Sporadic.HNSchreier.SylowCheckBase

public import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNSchreier.FALocalCheck
public import CFSG.Sporadic.HNSchreier.SylowData
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public meta import CFSG.Sporadic.HNSchreier.FALocalCheck
public meta import CFSG.Sporadic.HNSchreier.SylowData
public import CFSG.Sporadic.HNSchreier.SylowCheckInputs
public import Certificates.Certificate2108

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.F5.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native

theorem sylow_cert : sylowChecks (hnsData.orbit ()) = true :=
  Certificates.certificate2108

end CFSG.Sporadic.HNSchreier.Native
