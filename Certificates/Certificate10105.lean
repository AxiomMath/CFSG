module

public import CFSG.YGroups.Defs
import Certificates.Certificate10093
import Certificates.Certificate10100
import Certificates.Certificate10102
import Certificates.Kernel.Y442.Bound
import Certificates.Kernel.Y442.Data
import Certificates.Data.Kernel.TwistDce.Defs
import CFSG.Certificates.Kernel.YModel.Texts.YM432P
import CFSG.Certificates.Kernel.Common.HarnessGz
import CFSG.Certificates.Kernel.Common.Repo
public import Mathlib

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups in
theorem certificate10105 : Finite (YGroup 4 4 2) ∧ Nat.card (YGroup 4 4 2) ≤ 7531234255143970327756800 := KernelY442.y442_bound

end Certificates
