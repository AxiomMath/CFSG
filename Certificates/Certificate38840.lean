module

public import Certificates.Data.SmithE8MAbel
import Certificates.Kernel.SmithE8MK.Checks
import CFSG.Certificates.Kernel.SmithE8MKSound

public section

namespace Certificates

open CFSG.SmithE8M.K CertificateChecks.KernelSmithE8MK

theorem certificate38840 : CFSG.SmithE8M.e8mTabOK () = true ∧ CFSG.SmithE8M.e8mRACheck () = true ∧
    CFSG.SmithE8M.e8mAbelCheck () = true :=
  ⟨e8mTabOK_true, e8mRACheck_of ra_length ra_pos c7_le,
    e8mAbelCheck_of rows_ok pos_eq nra_eq chk28_ok chk26_ok⟩

end Certificates
