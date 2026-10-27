module

public import Certificates.Data.TwoF4LocCheck
public import CFSG.Sporadic.Schreier.TitsActionCheckInputs
public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
import Certificates.Kernel.TwoF4Loc.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier.Tits in
theorem certificate4181 : CFSG.TwoF4Loc.twoF4LocCheck titsLinePtArr titsGenArrs titsZArr = true := KernelTwoF4Loc.check

end Certificates
