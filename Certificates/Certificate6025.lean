module

public import CFSG.Monster.Existence.ELevelNativeInputs
import Certificates.Kernel.MonsterExist.ELevel.Check

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.B.TwoA.Census in
theorem certificate6025 : allOK = true := MonsterExist.ELevel.allOK_true

end Certificates
