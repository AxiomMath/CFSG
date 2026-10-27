module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.RealizeCheck
import Certificates.Kernel.MinusQuandle.Checks
import Certificates.Kernel.MinusRealize.Checks
import CFSG.Certificates.Kernel.MinusRealizeSound

public section

namespace Certificates

open CFSG.KC.MinusQuandle CertificateChecks.KernelMinusQ CertificateChecks.KernelMinusRZ in
open CFSG.OddTranspositions.PartThree.MinusRealize in
theorem certificate1383007 : realizeCheck () = true := by
  refine CFSG.KC.MinusRealize.realizeCheck_of (Pt := CFSG.KD.MinusRealize.pk true)
    (Pf := CFSG.KD.MinusRealize.pk false) rows_ok ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [force_eq] using pin_t
  · simpa only [force_eq] using sign_t
  · simpa only [force_eq] using table_t
  · simpa only [force_eq] using cover_t
  · simpa only [force_eq] using pin_f
  · simpa only [force_eq] using sign_f
  · simpa only [force_eq] using table_f
  · simpa only [force_eq] using cover_f

end Certificates
