
module

public import Certificates.Certificate2104Base

public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public meta import Certificates.Data.CFSGNative.Perm.Chain
import Certificates.Kernel.SporSch.HN.Prim2104
import Certificates.Kernel.SporSch.HN.Order2104
import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
import CFSG.Sporadic.HNSchreier.SeedsCheckInputs

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native in
open CFSG.ONSchreier.Native CFSG.Sporadic.F5.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native in
theorem certificate2104 : (primChecks (hnsData.orbit ()) = true)
    ∧ (orderChecks hnsData.n (natTab (hnsData.orbit ()).alpha)
      (natTab (hnsData.orbit ()).beta) = true
    ) :=
  ⟨KernelSporSch.HNPrim2104.primChecks_ok, KernelSporSch.HNOrd2104.orderChecks_ok⟩

end Certificates
