module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.ThreeBInputs
import Certificates.Certificate6007
import Certificates.Kernel.KDenseP.Norton
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.WordCheck
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native in
theorem certificate125369 :
    agreeAll (tbActPairs tbB1 tbXRows tbC1 [3, 4, 5]) = true := KernelKDenseP.Norton.c125369

end Certificates
