module

public import Certificates.Kernel.Co2Chain.He12636SylGen
public import CFSG.Certificates.Kernel.Spor.PackWord
public meta import Certificates.Kernel.Co2Chain.He12636SylGen
import CFSG.Certificates.Kernel.Common.Harness

public section

#knatlist CertificateChecks.KernelCo2Chain.He12636Syl.nats CertificateChecks.KernelCo2Chain.He12636Syl.natsM

namespace CertificateChecks.KernelCo2Chain.He12636Syl

@[expose] noncomputable def NF : Nat := nats.getD 0 0
@[expose] noncomputable def CJ : Nat := nats.getD 1 0
@[expose] noncomputable def CL : Nat := nats.getD 2 0
@[expose] noncomputable def MT : Nat := nats.getD 3 0
@[expose] noncomputable def PAR : Nat := nats.getD 4 0
@[expose] noncomputable def GEN : Nat := nats.getD 5 0
@[expose] noncomputable def DEP : Nat := nats.getD 6 0
@[expose] noncomputable def GI : Nat := nats.getD 7 0
@[expose] noncomputable def R : Nat := nats.getD 8 0

end CertificateChecks.KernelCo2Chain.He12636Syl

end
