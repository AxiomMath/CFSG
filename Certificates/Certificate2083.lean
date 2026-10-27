
module

public import Certificates.Certificate2083Base

public import CFSG.Sporadic.HNOddCore.CCheckInputs
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public import Certificates.Kernel.SporSch.HN.CTab
import Certificates.Kernel.SporSch.HN.CTabNeg
import CFSG.Sporadic.HNSchreier.InvolCheckInputs
meta import CFSG.Sporadic.HNSchreier.SeedsCheck
meta import CFSG.Sporadic.HNSchreier.LocalCheck
import CFSG.Sporadic.HNSchreier.LocalCheckInputs
meta import CFSG.Sporadic.HNSchreier.PrimCheck
meta import CFSG.Sporadic.HNSchreier.LocalData
meta import CFSG.Sporadic.HNSchreier.MaskCheck
import CFSG.Sporadic.HNSchreier.OrbitCheckInputs

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native in
open CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native in
open CFSG.Sporadic.F5.Native in
theorem certificate2083 : cChecksO (hnsData.orbit ()) = true := KernelSporSch.HNCTab.cChecks_ok

end Certificates
