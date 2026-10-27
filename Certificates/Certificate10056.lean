module

public import CFSG.RankThree.PartOne.KS.J2FiveCheckInputs
import Certificates.Kernel.Misc.Perm.J5

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.Native CFSG.RankThree.PartOne in
theorem certificate10056 :
    ((List.range 3).all (fun k => validA 315 j2FiveGensR[k]!) = true)
    ∧ (j2FiveQCheck j2FiveQCert = true)
    ∧ (j2FiveCentCheck 0 50 = true)
    ∧ (j2FiveCentCheck 1 50 = true)
    ∧ (j2FiveCentCheck 2 300 = true)
    ∧ (j2FiveCentCheck 3 300 = true)
    ∧ (j2FiveCentCheck 4 50 = true)
    ∧ (j2FiveCentCheck 5 300 = true)
    ∧ (j2FiveGoodCheck 0 (j2FiveCCert 0) j2FiveQCert = true)
    ∧ (j2FiveGoodCheck 1 (j2FiveCCert 1) j2FiveQCert = true)
    ∧ (j2FiveGoodCheck 4 (j2FiveCCert 4) j2FiveQCert = true)
    ∧ (j2FiveBadCheck 2 (j2FiveCCert 2) (j2FiveDCert 2) j2FiveQCert = true)
    ∧ (j2FiveBadCheck 3 (j2FiveCCert 3) (j2FiveDCert 3) j2FiveQCert = true)
    ∧ (j2FiveBadCheck 5 (j2FiveCCert 5) (j2FiveDCert 5) j2FiveQCert = true) := KernelMisc.J2F.facts

end Certificates
