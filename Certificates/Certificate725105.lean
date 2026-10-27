module

public import Certificates.Data.Sp6Insp443
import Certificates.Kernel.Sp6Insp443.OrbFacts

public section

open CFSG.SectionRank.QTK.Insp443.Sp6

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.QTK.Insp443.Sp6 in
theorem certificate725105 : chkOrb () = true := KernelS6I.chkOrb_true

end Certificates

end
