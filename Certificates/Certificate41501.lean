module

public import Certificates.Data.L34Borel
public meta import Certificates.Data.L34Borel
import Certificates.Kernel.LocalComp.L34Bo.Final
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace Certificates

open CertificateChecks

theorem certificate41501 : L34Borel.l34BorelCheck
    (CFSG.PSL3Four.Native.enumBFS 42 CFSG.PSL3Four.Native.gensS 20160).tabs = true := KernelLC.L34Bo.borel_true

end Certificates
