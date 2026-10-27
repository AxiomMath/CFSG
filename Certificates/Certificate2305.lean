module

public import CFSG.Sporadic.SuzOddCore.RelabelCheckInputs
import Certificates.Kernel.Sporadic.SuzK.Relabel

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native in
theorem certificate2305 : relabelOK (CFSG.Sporadic.Suz.Native.orbitData ()).alpha
    (CFSG.Sporadic.Suz.Native.orbitData ()).beta = true := KernelSpor.SuzK.relabel_ok

end Certificates
