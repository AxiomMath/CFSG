module

public import Certificates.Data.CFSGNative.AS91.M24Geom
import CFSG.Certificates.Kernel.M24G.StmtBSound
import Certificates.Kernel.M24G.TrioSextsEq
import Certificates.Kernel.M24G.StmtBChecks

public section

namespace CertificateChecks.Batch89016

open CFSG.KC.M24G

private theorem check_holds : CFSG.Quasithin.H13.AS91.M24G.Native.stmt313Check () = true := by
  rw [stmt313Check_eq trioList_eq trioSexts_eq sextList_eq]
  exact StmtBC.s313

end CertificateChecks.Batch89016

namespace Certificates

open CertificateChecks

theorem certificate89016 : CFSG.Quasithin.H13.AS91.M24G.Native.stmt313Check () = true :=
  CertificateChecks.Batch89016.check_holds

end Certificates
