module

public import Certificates.Data.CFSGNative.HN.Data
public import CFSG.Sporadic.HNSchreier.Data
public meta import Certificates.Data.CFSGNative.HN.Data
public meta import CFSG.Sporadic.HNSchreier.Data
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import Certificates.Certificate2102

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native

theorem orbit_cert : orbitCertChecks (hnsData.orbit ()) = true :=
  Certificates.certificate2102

end CFSG.Sporadic.HNSchreier.Native
