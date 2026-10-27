module

public import CFSG.Quasithin.Vol2.KGFactC31RuConfCheck
import Certificates.Kernel.SchreierFam.Ru7234F

public section

open CFSG.Quasithin.KGC31.Ru

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.KGC31.Ru in
theorem certificate7234 : m64Checks = true :=
  KernelSchreierFam.Ru7234.m64Checks_true

end Certificates

end
