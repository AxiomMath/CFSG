module

public import Certificates.Kernel.D4.ChainA
public import Certificates.Kernel.D4.EnumQ
public import Certificates.Kernel.D4.PhiData
public import Certificates.Kernel.D4.FieldData
public import Certificates.Data.Kernel.D4FieldK
public import Certificates.Data.Kernel.D4K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

theorem fieldOK : CFSG.KC.D4Field.fieldK (CFSG.KC.D4K.siftOK 2457 12 CA.LR CA.TRI CA.BP 7) EQ.T
    EQ.G (fun k => FX (2 + k)) (FX 0) (FX 1) (PH 0) CFSG.KD.D4F.NJ CFSG.KD.D4F.ZO
    CFSG.KD.D4F.ZL CFSG.KD.D4F.ZC CFSG.KD.D4F.ZP CFSG.KD.D4F.CD CFSG.KD.D4F.CR CFSG.KD.D4F.CN
    CFSG.KD.D4F.CW = true := by
  quickRfl

end CertificateChecks.KernelD4

end
