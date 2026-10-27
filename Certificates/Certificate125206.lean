module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.FiveTorusInputs
import Certificates.Certificate6007
import Certificates.Kernel.KDenseP.Norton
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.WordCheck
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native in
theorem certificate125206 :
    EdgeNoncomm.moveCheck (CFSG.AGLEmbedding.Norton.MON5_7.qW 0) (aV ()) = true ∧
      EdgeNoncomm.moveCheck (CFSG.AGLEmbedding.Norton.MON5_7.qW 1) (aV ()) = true ∧
      EdgeNoncomm.moveCheck (CFSG.AGLEmbedding.Norton.MON5_7.qW 2) (aV ()) = true := KernelKDenseP.Norton.c125206

end Certificates
