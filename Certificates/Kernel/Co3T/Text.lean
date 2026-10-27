module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.TextSound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeInputs
meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelCo3T.TT CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.co3TPermText
#ks_hexlines CertificateChecks.KernelCo3T.TT
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.co3TPermText 3 276 9

end
