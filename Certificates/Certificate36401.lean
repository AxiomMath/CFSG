module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4ModT10Data
import Certificates.Kernel.T10.Glue

public section

namespace Certificates

theorem certificate36401 : CFSG.OddStandard.AltStdSmall4.ModT10.t10CheckA () = true ∧
    CFSG.OddStandard.AltStdSmall4.ModT10.t10CheckB () = true ∧
    CFSG.OddStandard.AltStdSmall4.ModT10.t10CheckC () = true :=
  ⟨Kernel.T10.t10CheckA_kernel, Kernel.T10.t10CheckB_kernel, Kernel.T10.t10CheckC_kernel⟩

end Certificates
