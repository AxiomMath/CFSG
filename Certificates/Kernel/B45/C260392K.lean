module

public import Certificates.Data.Kernel.B45Perm.Defs
public import Certificates.Data.SmithB45ExcRuData
public import Certificates.Kernel.SporSch.Ru.Gens
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.B45.C260392

open CFSG.KC.B45P CFSG.Quasithin.B45Exc.Ru CertificateChecks.KernelSporSch.RuG

theorem b29K : b45OrdK 4060 12 29 [A0, A1] [A0I, A1I] A0 A0I ruB29W = true := by quickRfl

end CFSG.KD.B45.C260392

end
