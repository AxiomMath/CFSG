module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZCDefs
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.HSZC.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal in
theorem certificate42303 : ZCW CFSG.Blueprint.NativeSporadic.HS 7 :=
  HSZCK.zcw_HS_kernel

end Certificates
