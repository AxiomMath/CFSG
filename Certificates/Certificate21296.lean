module

public import CFSG.LargeExtraspecial.AS35WQP45Data
import Certificates.Certificate2012
import Certificates.Kernel.QP45W.Glue

public section

namespace Certificates

theorem certificate21296 : CFSG.LargeExtraspecial.AS35W.qp45InvCheck = true ∧
    CFSG.LargeExtraspecial.AS35W.qp45ProdCheck = true :=
  ⟨Kernel.QP45W.qp45InvCheck_true, Kernel.QP45W.qp45ProdCheck_true⟩

end Certificates
