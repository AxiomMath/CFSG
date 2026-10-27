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
theorem certificate125223 :
    (List.range 7).all (fun k => EdgeNoncomm.moveCheck (sevenNeXWord k) (aV ())) = true ∧
      (List.range 7).all (fun k => EdgeNoncomm.moveCheck (sevenNeYWord k) (aV ())) = true := KernelKDenseP.Norton.c125223

end Certificates
