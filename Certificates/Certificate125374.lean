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
theorem certificate125374 :
    agreeAll (tbActPairs tbB2 tbYRows tbC2 [8, 9, 10, 11]) = true := KernelKDenseP.Norton.c125374

end Certificates
