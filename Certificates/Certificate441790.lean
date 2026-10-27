module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10SpecD
import Certificates.Kernel.FzUT.Norm
import Certificates.Kernel.FzUT.FusionR12G
import Certificates.Kernel.FzUT.FusionR0G

public section

namespace Certificates

theorem certificate441790 : CFSG.OddStandard.SmallF3.FritzII.FzNormSpec ∧
    CFSG.OddStandard.SmallF3.FritzII.FzFusionSpec :=
  ⟨CFSG.OddStandard.SmallF3.FritzII.FzNorm.fzNormSpec,
    CFSG.KC.FzUT.fusion_of_r12 CFSG.KC.FzUT.fusion_r1 CFSG.KC.FzUT.fusion_r2⟩

end Certificates
