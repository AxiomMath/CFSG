module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L34CertInputs
public meta import Certificates.Data.CFSGNative.PSL3Four.Certificate
import Certificates.Kernel.LocalComp.L34Cos.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsL4U4 in
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four in
theorem certificate2005 : cosetCheck (enumBFS 42 gensS 20160).tabs (enumBFS 42 gTabs 241920).tabs = true := KernelLC.L34Cos.cosetCheck_true

end Certificates
