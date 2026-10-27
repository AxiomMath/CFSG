module

public import Certificates.Data.CFSGNative.MonsterAxis.CoPairData
public import Certificates.Data.Kernel.CoPair
import Certificates.Kernel.CoPair.W2

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.CoPair in
theorem certificate6045 : ∃ D : CFSG.KC.CoPair.OrbData,
    CFSG.KC.CoPair.orbOK Native.xWordN Native.yWordN Native.seedW2 4600 D = true := ⟨_, KernelCoPair.w2_ok⟩

end Certificates
