module

public import Certificates.Data.CFSGNative.MonsterAxis.Fi23Sp8
import Certificates.Kernel.Fi23P.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.Fi23Sp8 in
theorem certificate6062 : Native.sp8Entry () = true := KernelFi23P.sp8_true

end Certificates
