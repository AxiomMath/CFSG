module

public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.M11Local.Sub144
import Certificates.Kernel.M11Local.Codes
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs

public section

namespace Certificates

theorem certificate551201 : ∀ U : Subgroup ↥CFSG.Blueprint.NativeSporadic.M11, Nat.card U = 144 →
    CFSG.pCore 2 ↥U = ⊥ :=
  CFSG.KC.M11L.m11_sub144_pCore_of_check CertificateChecks.KernelM11Local.m11K_codes

end Certificates
