module

public import CFSG.Sporadic.HNSchreier.SylowCheck
public import CFSG.Sporadic.HNSchreier.PointwiseData
public meta import CFSG.Sporadic.HNSchreier.SylowCheck
public meta import CFSG.Sporadic.HNSchreier.PointwiseData
public import CFSG.Sporadic.HNSchreier.PointwiseCheckInputs
public import Certificates.Certificate2103

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.F5.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native

theorem pointwise_cert : pointwiseChecks (hnsData.orbit ()) = true :=
  Certificates.certificate2103

end CFSG.Sporadic.HNSchreier.Native
