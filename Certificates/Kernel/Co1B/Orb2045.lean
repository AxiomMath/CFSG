module

public import Certificates.Kernel.Sporadic.RawGenOrb
public import CFSG.Sporadic.Co1Block.TwoBData
public meta import CFSG.Sporadic.Co1Block.TwoBCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Assembly.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Tri2045

meta def baseM : Array Nat := CFSG.Sporadic.Co1Block.twoBChainBase.toArray

end CertificateChecks.KernelCo1B.Tri2045

#ks_raworb CertificateChecks.KernelCo1B.Tri2045.RO 1365 11 128 CFSG.Sporadic.Co1Block.twoBStrong
  CertificateChecks.KernelCo1B.Tri2045.baseM 2 CFSG.Sporadic.Co1Block.twoBChainWords

end
