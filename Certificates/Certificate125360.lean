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
theorem certificate125360 :
    agreeAll tbOrderPairs = true ∧
      agreeAll tbWOrderPairs = true ∧
      (EdgeNoncomm.moveCheck tbW (aV ()) || EdgeNoncomm.moveCheck tbW (CFSG.YGroups.Y443Native.bV ()) ||
        EdgeNoncomm.moveCheck tbW (wV ())) = true := KernelKDenseP.Norton.c125360

end Certificates
