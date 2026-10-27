module

public import Certificates.Kernel.Co1B.Dag2047
public import Certificates.Data.Kernel.SporSch.Co1Tower
public meta import Certificates.Kernel.SporSch.Co1.GenTower
meta import Certificates.Kernel.Co1B.In2047
meta import CFSG.Sporadic.Co1Block.TwoCData
public import Certificates.Kernel.SporSch.Co1.GenTower
import CFSG.Assembly.Defs

public section

set_option maxRecDepth 400000

#kss_co1tower CertificateChecks.KernelCo1B.C2047.TW CertificateChecks.KernelCo1B.C2047.dag₂
  CertificateChecks.KernelCo1B.C2047.D2.M CFSG.Sporadic.Co1Block.twoCVBase
  CFSG.Sporadic.Co1Block.twoCVGens CFSG.Sporadic.Co1Block.twoCVSizes 42 512

end
