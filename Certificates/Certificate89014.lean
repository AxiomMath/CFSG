module

public import Certificates.Data.CFSGNative.AS91.M24Geom
import CFSG.Certificates.Kernel.M24G.StmtBSound
import Certificates.Kernel.M24G.TrioSextsEq
import Certificates.Kernel.M24G.StmtBChecks

public section

namespace CertificateChecks.Batch89014

open CFSG.KC.M24G

private theorem check_holds : CFSG.Quasithin.H13.AS91.M24G.Native.stmt310Check () = true := by
  rw [stmt310Check_eq trioList_eq trioSexts_eq sextList_eq TrioC.length
    (replay_facts trioReplay_ok).1 StmtBC.trio_lt]
  exact StmtBC.s310

end CertificateChecks.Batch89014

namespace Certificates

open CertificateChecks

theorem certificate89014 : CFSG.Quasithin.H13.AS91.M24G.Native.stmt310Check () = true :=
  CertificateChecks.Batch89014.check_holds

end Certificates
