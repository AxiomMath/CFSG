module

public import Certificates.Data.Kernel.Co1BInner
public import Certificates.Kernel.Co1B.Data21159
public import Certificates.Kernel.Co1B.Cnt21142
import Certificates.Kernel.J4Q.AllN

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1B

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KD.Co1B CFSG.Sporadic.Co1Patterson.TwistNative

@[expose] noncomputable def lpK (c : Nat) : Bool :=
  strictB (hpK c) fun H => (aList.zip AP59).all fun pa => strictB (mulWK H pa.2) fun r =>
    loopK T59 [oneK, AL42, W0L42, W0AL42] AL42 W0L42 G159 G259 K159 RX59 RY59 (isVP c pa.1) r

#j4q_all CFSG.KD.Co1B.LP59 CertificateChecks.KernelCo1B.lpK 64

end CertificateChecks.KernelCo1B

end
