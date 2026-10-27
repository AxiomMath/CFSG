module

public import Certificates.Data.CFSGNative.PSL3Four.L34Aut
import Certificates.Kernel.LocalComp.L34Aut.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.PSL3Four.Native in
theorem certificate5180 : l34AutCheck (enumBFS 42 gensS 20160).tabs (enumBFS 42 gTabs 241920).tabs = true := KernelLC.L34Aut.aut_true

end Certificates
