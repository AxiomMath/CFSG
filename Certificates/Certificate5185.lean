module

public import Certificates.Data.CFSGNative.PSL3Four.L34Ord
import Certificates.Kernel.LocalComp.L34Ord.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.PSL3Four.Native in
theorem certificate5185 : l34OrdCheck (enumBFS 42 gensS 20160).tabs = true := KernelLC.L34Ord.ord_true

end Certificates
