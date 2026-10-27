module

public import Certificates.Kernel.Co2HeavyK.Data
public import CFSG.Certificates.Kernel.Co1F2Sound

public section

namespace CertificateChecks.KernelCo2HeavyK

open CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native

theorem ta_eq : transposeRows 22 (unpackR 22 (MT 0)) = unpackR 22 (MT 4) := by decide +kernel

theorem tb_eq : transposeRows 22 (unpackR 22 (MT 1)) = unpackR 22 (MT 5) := by decide +kernel

end CertificateChecks.KernelCo2HeavyK

end
