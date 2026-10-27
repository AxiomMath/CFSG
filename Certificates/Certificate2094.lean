
module

public import Certificates.Certificate2094Base

public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import Certificates.Kernel.SporSch.HN.Pt2094
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
theorem certificate2094 : xChecksO (hnsData.orbit ()) = true := KernelSporSch.HNPt2094.xChecks_ok

end Certificates
