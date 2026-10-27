module

public import Certificates.Data.Seitz77L34V1Act
public meta import Certificates.Data.Seitz77L34V1Act
import Certificates.Kernel.LocalComp.L34V1.Final
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace Certificates

open CertificateChecks

theorem certificate6127 : Seitz77L34.l34V1ActCheck
    (CFSG.PSL3Four.Native.enumBFS 42 CFSG.PSL3Four.Native.gTabs 241920).tabs = true := KernelLC.L34V1.v1Act_true

end Certificates
