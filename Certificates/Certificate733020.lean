module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5ArithLab
import CFSG.Certificates.Kernel.Str83G5TypeKSound
import Certificates.Kernel.Direct.C733020

public section

namespace Certificates

open CertificateChecks

theorem certificate733020 : CFSG.Quasithin.Stroth.G5.typeCheck () = true :=
  CFSG.Quasithin.Stroth.G5.K.typeCheck_of_fullK KernelDirect.C733020.ch733020full

end Certificates
