module

public import Certificates.Data.CFSGNative.PSL3Four.L34Syl
import Certificates.Kernel.LocalComp.L34Syl.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.PSL3Four.Native in
theorem certificate5183 : l34SylCheck (enumBFS 42 gensS 20160).tabs = true := KernelLC.L34Syl.syl_true

end Certificates
