module

public import Certificates.Data.K426J3
public import CFSG.Certificates.CosetTableCompactPresented
import Certificates.Kernel.CosetW.Assembly

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.CosetTable in
theorem certificate8059 : cyclicCheckC j3tLiftRels [2] 4 2000 90 = true := CosetW.proof8059

end Certificates
