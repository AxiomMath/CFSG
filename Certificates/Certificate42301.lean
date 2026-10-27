module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZCDefs
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MZC.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal in
theorem certificate42301 : ZCW ↥CFSG.Blueprint.NativeSporadic.M22 5 ∧ ZCW ↥CFSG.Blueprint.NativeSporadic.M22 7 ∧
    ZCW ↥CFSG.Blueprint.NativeSporadic.M23 5 :=
  ⟨MZCK.zcw_m22_5, MZCK.zcw_m22_7, MZCK.zcw_m23_5⟩

end Certificates
