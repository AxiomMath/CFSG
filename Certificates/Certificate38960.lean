module

public import CFSG.GF2Type.Widths1112.Co2Module.EnumInputs
import Certificates.Kernel.Co2Span.Glue
public import CFSG.Sporadic.HS.SmallF2Spec

public section

namespace Certificates

open CertificateChecks

open CFSG.GF2Type.Widths1112.Co2Module CFSG.GF2W1112 CFSG.Sporadic.SmallF2 in
theorem certificate38960 : ∀ M : Matrix (Fin 22) (Fin 22) (ZMod 2),
    (∀ k : Fin 3, M * uXOf 1 (iY k) = uXOf 1 (iZ k) * M) →
      ∃ c : Fin 11 → ZMod 2, M = ∑ i : Fin 11, c i • CFSG.Sporadic.SmallF2.rowsMatrix 22 (w12UBRows[i.val]!) := KernelCo2Span.span38960

end Certificates
