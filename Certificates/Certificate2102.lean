module

public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
import Certificates.Kernel.SporSch.HN.OrbCert

public section

namespace Certificates

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native in
open CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native in
theorem certificate2102 : orbitCertChecks (hnsData.orbit ()) = true :=
  CertificateChecks.KernelSporSch.HNXCert.hns_orbitCert

end Certificates
