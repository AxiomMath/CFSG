module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenDatum
import Certificates.Certificate6007
import Certificates.Kernel.KDenseP.Norton
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.WordCheck
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native in
theorem certificate125221 :
    agreeAll sevenYPairs = true ∧
      agreeAll sevenIPairs = true := KernelKDenseP.Norton.c125221

end Certificates
