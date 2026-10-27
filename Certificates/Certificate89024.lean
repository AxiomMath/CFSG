module

public import Certificates.Data.CFSGNative.AS91.M24Fuse
import Certificates.Kernel.M24G.FuseInv
import Certificates.Kernel.M24G.FuseTodd

public section

namespace CertificateChecks.Batch89024

open CFSG.KC.M24G.FuseC CFSG.Quasithin.H13.AS91.M24G

private theorem check_holds : Native.fuseCheck () = true := by
  unfold Native.fuseCheck
  simp only [fuseCommCheck_ok, fuseDuadCheck_ok, fusePiCheck_ok, fuseInvCheck_ok, fuseX0Check_ok,
    fusePiBCheck_ok, fusePiACheck_ok, Bool.and_self]

end CertificateChecks.Batch89024

namespace Certificates

open CertificateChecks

theorem certificate89024 : CFSG.Quasithin.H13.AS91.M24G.Native.fuseCheck () = true :=
  CertificateChecks.Batch89024.check_holds

end Certificates
