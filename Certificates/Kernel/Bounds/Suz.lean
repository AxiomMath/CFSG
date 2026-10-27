module

public import Certificates.Kernel.Bounds.Data.Suz
import Certificates.Kernel.Bounds.Assemble
import Certificates.Kernel.Bounds.Suz.T1vK000
import Certificates.Kernel.Bounds.Suz.T2vK000
import Certificates.Kernel.Bounds.Suz.T3vK000
import Certificates.Kernel.Bounds.Suz.T4vK000

public section

namespace CertificateChecks.KernelBounds.Suz

#kb_assemble CFSG.KBRoute.Suz T1 Suz_T1v include_bytes "Suz/data/Suz_T1v.meta" 3149 9308309354496609925 CFSG.KBRoute.Suz.rels CertificateChecks.KernelBounds.Suz.t1
#kb_assemble CFSG.KBRoute.Suz T2 Suz_T2v include_bytes "Suz/data/Suz_T2v.meta" 729 17567991394435746506 CFSG.KBRoute.Suz.rels CertificateChecks.KernelBounds.Suz.t2
#kb_assemble CFSG.KBRoute.Suz T3 Suz_T3v include_bytes "Suz/data/Suz_T3v.meta" 431 2536992008051246648 CFSG.KBRoute.Suz.rels CertificateChecks.KernelBounds.Suz.t3
#kb_assemble CFSG.KBRoute.Suz T4 Suz_T4v include_bytes "Suz/data/Suz_T4v.meta" 5057 4390005806162259891 CFSG.KBRoute.Suz.rels CertificateChecks.KernelBounds.Suz.t4

open CFSG.KBRoute.Suz in
theorem facts_holds : CFSG.KBRoute.Suz.facts :=
  ⟨t1, t2, t3, t4, top, top_T2, top_T3, top_T4, link_T1, link_T2, link_T3⟩

end CertificateChecks.KernelBounds.Suz

end
