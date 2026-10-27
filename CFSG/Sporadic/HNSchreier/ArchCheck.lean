module

public import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public import CFSG.Sporadic.HNSchreier.ArchCheckInputs
public import Certificates.Certificate2095

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native

theorem arch_data_cert : archDataChecks (hexDumpBytes arraysPayload) = true :=
  Certificates.certificate2095.1

theorem arch_eq_cert : archEqChecks (hexDumpBytes arraysPayload) (hnsData.orbit ()) = true :=
  Certificates.certificate2095.2

end CFSG.Sporadic.HNSchreier.Native
