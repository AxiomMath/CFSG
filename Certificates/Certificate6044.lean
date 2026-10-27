module

public import Certificates.Data.CFSGNative.MonsterAxis.CoPairData
public import Certificates.Data.Kernel.CoPair
import Certificates.Kernel.CoPair.W1

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.CoPair in
theorem certificate6044 : ∃ D : CFSG.KC.CoPair.OrbData,
    CFSG.KC.CoPair.orbOK Native.xWordN Native.yWordN Native.seedW1 47104 D = true := ⟨_, KernelCoPair.w1_ok⟩

end Certificates
