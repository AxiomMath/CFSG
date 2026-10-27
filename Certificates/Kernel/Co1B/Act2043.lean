module

public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Kernel.Co1B.Acts1
public import Certificates.Kernel.Co1B.Data2041
public import Certificates.Kernel.Co1B.Data2043
public import Certificates.Data.Kernel.Co1BAct
public import Certificates.Kernel.J4Q.AllN

public section

namespace CertificateChecks.KernelCo1B

@[expose] noncomputable def actOK (j : Nat) : Bool :=
  CFSG.KC.Co1B.actChunkK CV.F CFSG.KD.Co1B.T1 CFSG.KD.Co1B.TB (CV.F j) (AC.F j) (AC1.F j)

end CertificateChecks.KernelCo1B

#j4q_all CertificateChecks.KernelCo1B.Act CertificateChecks.KernelCo1B.actOK 117

end
