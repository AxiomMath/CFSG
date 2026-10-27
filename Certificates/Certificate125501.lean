module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ThirteenCheckDefs
import Certificates.Certificate6007
import Certificates.Kernel.KDenseP.Norton

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.Norton.MON11_13 in
theorem certificate125501 :
    thirteenRelCheck () = true := KernelKDenseP.Norton.c125501

end Certificates
