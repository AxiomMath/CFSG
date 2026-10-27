module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319SpecA
import Certificates.Kernel.FzUT.Norm
import Certificates.Kernel.FzUT.ClassA
import Certificates.Kernel.FzUT.AutW

public section

namespace Certificates

theorem certificate441782 : CFSG.OddStandard.SmallF3.FritzII.FzNormSpec ∧
    CFSG.OddStandard.SmallF3.FritzII.FzClassSpecA :=
  ⟨CFSG.OddStandard.SmallF3.FritzII.FzNorm.fzNormSpec,
    CFSG.KC.FzUT.classA_of_autW CFSG.KC.FzUT.autW_reps⟩

end Certificates
