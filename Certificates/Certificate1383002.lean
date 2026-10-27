module

public import CFSG.OddTranspositions.PartThree.Eleven.Plus.QuandleCheck
import Certificates.Kernel.PlusQuandle.Checks

public section

namespace Certificates

open CertificateChecks.KernelPlusQ in
theorem certificate1383002 :
    CFSG.OddTranspositions.PartThree.plusQuandleNoncommCheck () = true ∧
    CFSG.OddTranspositions.PartThree.plusQuandlePrimitiveCheck () = true ∧
    CFSG.OddTranspositions.PartThree.plusQuandlePerpCheck () = true :=
  ⟨noncomm_ok, CFSG.KC.PlusQuandle.primitive_of rows_ok prim_ok,
    CFSG.KC.PlusQuandle.perp_of rows_ok deriv_ok fun _ ha => perp_all ha⟩

end Certificates
