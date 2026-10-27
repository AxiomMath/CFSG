
module

public import Certificates.Certificate2109Base

public import CFSG.Sporadic.HNSchreier.ThreeCheckInputs
public meta import CFSG.Sporadic.HNSchreier.LocalCheckBase
public meta import CFSG.Sporadic.HNSchreier.FAData
import Certificates.Kernel.SporSch.HN.Pt2109
import CFSG.Sporadic.HNSchreier.OrbitCheckInputs

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native in
open CFSG.ONSchreier.Native CFSG.Sporadic.F5.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native in
theorem certificate2109 : threeChecks (hnsData.orbit ()) = true :=
  KernelSporSch.HNPt2109.threeChecks_ok

end Certificates
