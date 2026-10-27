
module

public import Certificates.Certificate2108Base

public import CFSG.Sporadic.HNSchreier.SylowCheckInputs
public meta import CFSG.Sporadic.HNSchreier.ThreeCheckBase
public meta import CFSG.Sporadic.HNSchreier.FALocalCheckBase
public meta import CFSG.Sporadic.HNSchreier.SylowData
public import Certificates.Kernel.SporSch.HN.Pt2108
import CFSG.Sporadic.HNSchreier.OrbitCheckInputs

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native in
open CFSG.ONSchreier.Native CFSG.Sporadic.F5.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native in
theorem certificate2108 : sylowChecks (hnsData.orbit ()) = true := KernelSporSch.HNPt2108.sylow_ok

end Certificates
