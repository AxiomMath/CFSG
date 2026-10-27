
module


public import Certificates.Data.CFSGNative.Fi22.Local
import Certificates.Kernel.T46K.Chain

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native CFSG.Perm.Native CFSG.F4.Native in
theorem certificate1009 : (uPtsOK && CFSG.Perm.Native.chainOK 693 t46Letters t46Base t46Q t46Base t46Trees 3 &&
    orbitSizes t46Trees == [693, 512, 120, 36, 6]) = true := KernelT46.t46_chain

end Certificates
