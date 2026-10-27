module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BInvCentData

public section

open CFSG.Monster.B.CTIB.Native

namespace CertificateChecks.Batch27200

open CFSG.Monster.B.CTIB.Native

theorem a5_0 : a5OK () = true := by
  decide +kernel

end CertificateChecks.Batch27200

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.CTIB.Native in
theorem certificate27200 : a5OK () = true := CertificateChecks.Batch27200.a5_0

end Certificates
