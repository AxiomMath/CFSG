module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.QuandleCheck
import Certificates.Kernel.MinusQuandle.Checks

public section

namespace Certificates

open CertificateChecks.KernelMinusQ in
theorem certificate1383010 :
    CFSG.OddTranspositions.PartThree.minusQuandleNoncommCheck () = true ∧
    CFSG.OddTranspositions.PartThree.minusQuandlePrimitiveCheck () = true ∧
    CFSG.OddTranspositions.PartThree.minusQuandlePerpCheck () = true :=
  ⟨noncomm_ok, CFSG.KC.MinusQuandle.primitive_of rows_ok prim_ok,
    CFSG.KC.MinusQuandle.perp_of rows_ok deriv_ok fun _ ha => perp_all ha⟩

end Certificates
