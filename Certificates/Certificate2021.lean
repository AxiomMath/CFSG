module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34CertInputs
import Certificates.Kernel.LocalComp.L34ScanFinal
public import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.GrSLit CFSG.PSL3Four in
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four in
theorem certificate2021 : twoCentralOK (enumBFS 42 gTabs 241920).tabs
    (centTabs 42 (enumBFS 42 gensS 20160).tabs r₁T) = true := KernelLC.L34Scan.twoCentral_true

end Certificates
