module

public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.E27J3Syl.D
meta import Certificates.Kernel.J3Ref.Bind
import Certificates.Kernel.E27J3Syl.D
import Certificates.Kernel.J3Ref.Bind

namespace CFSG.KD.E27J3S.D

meta def hvM : Array (Array Nat) := CertificateChecks.KernelJ3Ref.hvOfM recS

end CFSG.KD.E27J3S.D

public section

#kmisc_packarrs CFSG.KD.E27J3S.SEV CFSG.KD.E27J3S.D.hvM 64

end
