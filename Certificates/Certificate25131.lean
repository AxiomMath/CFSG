module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Data11Native
import CFSG.Certificates.Kernel.J4Mask11Sound
import Certificates.Kernel.J4Mask11.Check

public section

namespace Certificates

open CFSG.EvenSporadicStandard.J4Std.Data11 CertificateChecks.KernelJ4Mask11 CFSG.KC.J4Mask11

open CFSG.EvenSporadicStandard.J4Std.Data11 in
theorem certificate25131 : chkMask = true :=
  decide_eq_true ⟨mf1, mf2, mf3, mf4, mf5, mask6_of mask6_ok, mask7_of mask7_ok,
    mask8_of mask8_ok mask8w_ok⟩

end Certificates
