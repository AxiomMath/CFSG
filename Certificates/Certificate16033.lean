
module

public import Certificates.Certificate16033Base
import all Certificates.Certificate16033Base


public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.Code CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert

public section


open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.Code CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert

namespace CertificateChecks.Batch16033

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.Code CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert

end CertificateChecks.Batch16033

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.Code CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert in
theorem certificate16033 : (
    Native.actD 22 (genQuotMatrix 23) 31 = 31 ^^^ 12288
  ) ∧ (
    Native.actD 22 (genQuotMatrix 23) 12288 = 12288
  ) := by
  exact ⟨CertificateChecks.Batch16033.alpha23K_wFr_0, CertificateChecks.Batch16033.alpha23K_sW_1⟩

end Certificates
