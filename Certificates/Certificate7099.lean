module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneA7Raw
import Certificates.Kernel.Misc.A7Nat
import CFSG.Certificates.Kernel.Misc.A7NatSound

public section

namespace Certificates

open CertificateChecks.KernelA7Nat in
theorem certificate7099 : CFSG.Quasithin.H13.A7Mod.A7Raw :=
  CFSG.KC.A7Nat.a7Raw_of stabK_2 stabK_4 stabK_6 orbK_true s0K_true fixK_true uK_1 uK_2
    uK_3 cenK_true yK_true

end Certificates
