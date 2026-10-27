module

public import Certificates.Data.FzL410Norm
import CFSG.Certificates.Kernel.FzL410.Norm
import Certificates.Kernel.FzL410.Stages

public section

namespace Certificates

open CertificateChecks

theorem certificate441787 : FzL410.NormTriple :=
  ⟨CFSG.FzL410K.normSpec FzL410K.normInj_true, CFSG.FzL410K.stageA_of FzL410K.stageA_true,
    CFSG.FzL410K.stageB_of FzL410K.stageB_true⟩

end Certificates
