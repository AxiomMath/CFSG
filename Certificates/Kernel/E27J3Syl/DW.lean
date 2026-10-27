module

public import Certificates.Kernel.Sporadic.IntWordsCmd
meta import Certificates.Kernel.E27J3Syl.D
meta import Certificates.Kernel.J3Ref.Bind
import Certificates.Kernel.E27J3Syl.D
import Certificates.Kernel.J3Ref.Bind

namespace CFSG.KD.E27J3S.D

meta def swM : Array (List Int) :=
  #[0, 1, 3, 4, 6, 7].map fun k => CertificateChecks.KernelJ3Ref.siftWordM syM[k]!

end CFSG.KD.E27J3S.D

public section

#kc_intwords CFSG.KD.E27J3S.SW CFSG.KD.E27J3S.D.swM

end
