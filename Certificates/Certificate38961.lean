module

public import CFSG.GF2Type.Widths1112.Co2Module.EnumInputs
import Certificates.Kernel.Co2Span.Glue
public import CFSG.Sporadic.HS.SmallF2Spec

public section

namespace Certificates

open CertificateChecks

open CFSG.GF2Type.Widths1112.Co2Module CFSG.GF2W1112 CFSG.Sporadic.SmallF2 in
theorem certificate38961 : ∀ (c : Fin 11 → ZMod 2) (θ : Fin 2 → Matrix (Fin 2) (Fin 2) (ZMod 2)),
    (∑ i : Fin 11, c i • CFSG.Sporadic.SmallF2.rowsMatrix 22 (w12UBRows[i.val]!)) ^ 3 = 1 →
    (∀ j, (CFSG.GF2Type.Widths1112.Co2Module.wordProd (fun s => uXOf (θ s) (iN s)) (uTw j) *
      ∑ i : Fin 11, c i • CFSG.Sporadic.SmallF2.rowsMatrix 22 (w12UBRows[i.val]!)) ^ uKk j = 1) →
    ∃ S : Matrix (Fin 2) (Fin 2) (ZMod 2), IsUnit S ∧
      (∀ s, Qfin S * uXOf (θ s) (iN s) = uX0 s * Qfin S) ∧
      Qfin S * (∑ i : Fin 11, c i • CFSG.Sporadic.SmallF2.rowsMatrix 22 (w12UBRows[i.val]!)) =
        CFSG.Sporadic.SmallF2.rowsMatrix 22 w12UM0Rows * Qfin S := KernelCo2Span.enum38961

end Certificates
