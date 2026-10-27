
module

public import CFSG.Sporadic.HNSchreier.LocalCheckBase

public import CFSG.Sporadic.HNSchreier.PrimCheck
public import CFSG.Sporadic.HNSchreier.LocalData
public import CFSG.Sporadic.HNSchreier.MaskCheck
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public import Certificates.Certificate2100

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native

theorem label_cert : labelChecks = true :=
  Certificates.certificate2100.1

theorem local_cert_orbit : localChecksO (hnsData.orbit ()) = true :=
  Certificates.certificate2100.2

theorem local_cert : localChecks hnsData.n (natTab (hnsData.orbit ()).alpha)
    (natTab (hnsData.orbit ()).beta) = true := local_cert_orbit

end CFSG.Sporadic.HNSchreier.Native
