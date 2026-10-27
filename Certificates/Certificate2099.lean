
module

public import Certificates.Certificate2099Base

public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public meta import CFSG.Sporadic.HNSchreier.LocalCheckBase
public import Certificates.Kernel.SporSch.HN.Invol2099

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native in
open CFSG.Sporadic.He.Native CFSG.ONSchreier.Native in
theorem certificate2099 : involChecks rowsA rowsB (rowsOf 5 133 LocalData.normalizerPayload)
    (rowsOf 5 133 LocalData.involutionPayload) tauIdx labMasks = true := KernelSporSch.HNInvol.facts

end Certificates
