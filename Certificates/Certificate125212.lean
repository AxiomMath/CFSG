module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenData
import Certificates.Certificate6007
import Certificates.Kernel.KDenseP.Norton
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.WordCheck
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native in
theorem certificate125212 :
    EdgeNoncomm.moveCheck dW (aV ()) = true ∧
      EdgeNoncomm.moveCheck CFSG.AGLEmbedding.Norton.MON5_7.zW (aV ()) = true ∧
      (List.range 7).all (fun k => EdgeNoncomm.moveCheck (sevenNeWord k) (aV ())) = true := KernelKDenseP.Norton.c125212

end Certificates
