module

public import Certificates.Data.L34Unitary
public meta import Certificates.Data.L34Unitary
import Certificates.Kernel.LocalComp.L34Un.Final
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace Certificates

open CertificateChecks

theorem certificate41503 : L34Unitary.l34UnitaryCheck
    (CFSG.PSL3Four.Native.enumBFS 42 CFSG.PSL3Four.Native.gensS 20160).tabs
    (CFSG.PSL3Four.Native.enumBFS 42 CFSG.PSL3Four.Native.gTabs 241920).tabs = true := KernelLC.L34Un.unitary_true

end Certificates
