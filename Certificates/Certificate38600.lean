module

public import Certificates.Data.SmithL6Check
import CFSG.Certificates.Kernel.SmithL6KTSound

public section

namespace Certificates

theorem certificate38600 : CFSG.SmithL6.chkTvList = true ∧ CFSG.SmithL6.chkTvImg = true :=
  ⟨CFSG.SmithL6.K.chkTvList_holds, CFSG.SmithL6.K.chkTvImg_holds⟩

end Certificates
