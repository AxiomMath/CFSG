module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONOrderEightCheck
import Certificates.Kernel.Sporadic.ONOrd.Ord27142

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Induction CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native in
theorem certificate27142 : onOrderEightOK (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).alpha)
    (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).beta) = true := KernelSpor.ONOrd.ord27142

end Certificates
