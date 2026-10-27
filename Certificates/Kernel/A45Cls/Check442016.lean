module

public import Certificates.Kernel.A45Cls.Cls
public import Certificates.Kernel.A45Cls.Data442016
public import Certificates.Data.Kernel.A45Cls.Outer
public import Certificates.Data.Kernel.PermCent.B0Twin
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KC.A45Cls CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.B0T CFSG.ComponentClassification.CatFactsSmall.PSp43

theorem kB16 : (Outer442016.K16.B == blC.map Subtype.val) = true := by quickRfl

theorem kOut36 : outL 36 K36.T Outer442016.K16.B = true := by quickRfl

theorem kOut540 : outL 540 K540.T Outer442016.K16.B = true := by quickRfl

theorem kTA : siftC QP45 (cOf (Certificates.P43Twin.tA ())) 0 = true := by quickRfl

theorem kTB : siftC QP45 (cOf (Certificates.P43Twin.tB ())) 0 = true := by quickRfl

end CertificateChecks.KernelA45

end
