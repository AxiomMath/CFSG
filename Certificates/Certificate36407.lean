module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2ModZData
import Certificates.Kernel.ModZ.Glue

public section

namespace Certificates

theorem certificate36407 : CFSG.OddStandard.AltStdSmall4.G2.z4CheckE () = true ∧
    CFSG.OddStandard.AltStdSmall4.G2.z4CheckC () = true ∧
    CFSG.OddStandard.AltStdSmall4.G2.z8CheckC (-1) () = true ∧
    CFSG.OddStandard.AltStdSmall4.G2.z8CheckC CFSG.OddStandard.AltStdSmall4.G2.Z8M.uThree () = true :=
  ⟨Kernel.ModZ.z4CheckE_kernel, Kernel.ModZ.z4CheckC_kernel, Kernel.ModZ.z8CheckC_neg_one_kernel,
    Kernel.ModZ.z8CheckC_three_kernel⟩

end Certificates
