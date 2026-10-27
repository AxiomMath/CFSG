module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZCDefs
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.J2ZC.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal in
theorem certificate42302 : ZCW CFSG.Blueprint.NativeSporadic.J2 7 :=
  J2ZCK.zcw_J2_kernel

end Certificates
