module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6SimpleWeylCheck
import Certificates.Kernel.Direct.C63001

public section

namespace Certificates

open CertificateChecks

theorem certificate63001 : CFSG.HardMathSupport.Timmesfeld.Tables.T1b.e6SimpleCheck () = true :=
  KernelDirect.C63001.e6SimpleCheck_eq_true

end Certificates
