module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative
import Certificates.Kernel.LocalComp.J2DispT
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.J2Cover.Models in
theorem certificate10026 :
    (bitAt fRows 2 16 && !bitAt fRows 16 2) = false ∧
      (!bitAt fRows 2 16 && bitAt fRows 16 2) = true := KernelLC.cert10026_proved

end Certificates
