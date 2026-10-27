module

public import Certificates.Data.RuInsp443
import Certificates.Kernel.RuInsp443.Facts

public section

open CFSG.Quasithin.KGC31.Ru

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.KGC31.Ru in
theorem certificate725102 : chkKxE () = true := KernelRuInsp.chkKxE_true

end Certificates

end
