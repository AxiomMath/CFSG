module

public import CFSG.Sporadic.HNSchreier.SylowCheck
public import CFSG.Sporadic.HNSchreier.IntrinsicData
public meta import CFSG.Sporadic.HNSchreier.SylowCheck
public meta import CFSG.Sporadic.HNSchreier.IntrinsicData
public import CFSG.Sporadic.HNSchreier.IntrinsicCheckInputs
public import Certificates.Certificate2098

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.F5.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native

theorem intrinsic_cert : intrinsicChecks (hnsData.orbit ()) = true :=
  Certificates.certificate2098

end CFSG.Sporadic.HNSchreier.Native
