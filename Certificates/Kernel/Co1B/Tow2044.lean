module

public import Certificates.Kernel.Co1B.Dag2044
public import Certificates.Data.Kernel.SporSch.Co1Tower
public meta import Certificates.Kernel.SporSch.Co1.GenTower
meta import Certificates.Kernel.Co1B.In2044
meta import CFSG.Sporadic.Co1Block.TwoAData
public import Certificates.Kernel.SporSch.Co1.GenTower
import CFSG.Assembly.Defs

public section

set_option maxRecDepth 400000

#kss_co1tower CertificateChecks.KernelCo1B.C2044.TW CertificateChecks.KernelCo1B.C2044.dag₂
  CertificateChecks.KernelCo1B.C2044.D2.M CFSG.Sporadic.Co1Block.twoAVBase
  CFSG.Sporadic.Co1Block.twoAVGens CFSG.Sporadic.Co1Block.twoAVSizes 35 512

end
