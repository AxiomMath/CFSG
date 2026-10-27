module

public import Certificates.Kernel.AE6ModC.Checks
public import Certificates.Kernel.AE6Sm.Chain
public import Certificates.Data.Kernel.AE6C2N

public section

namespace CertificateChecks.KernelAE6C2

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.KGC31P CFSG.KC.AE6F CFSG.KC.AE6C2
  Certificates.AE6Model
open CertificateChecks.KernelAE6F (RG)
open CertificateChecks.KernelAE6ModC (PLL)

@[expose] def BZ : List Nat := [0, 2, 4, 24, 8]

@[expose] noncomputable def CZL : List (List Nat) :=
  trPL 360 9 CertificateChecks.KernelAE6Sm.CZ.LR CertificateChecks.KernelAE6Sm.CZ.TR 5

@[expose] noncomputable def QS : List (List Nat) := qsAllN PLL RG

@[expose] def L3I : List Nat :=
  [41, 42, 371, 368, 353, 354, 467, 464, 48, 51, 93, 94, 125, 126, 433, 434, 9, 10, 271, 268, 245,
    246, 197, 198, 174, 173, 290, 289, 332, 335, 508, 511]

@[expose] noncomputable def LSP : List (List Nat) :=
  let A := [PLL.getD 335 0, PLL.getD 511 0]
  [A, A, A, L3I.map fun k => PLL.getD k 0, A, A, A, A]

@[expose] noncomputable def GTN : List (Nat × Nat) := RG.map fun g => (g, invN 360 9 g)

@[expose] noncomputable def TGN : List (List Nat × Nat) := pWordsC2.map fun w => (w, awN RG w)

@[expose] noncomputable def ZCN : List Nat :=
  (List.range 8).map fun i =>
    pmN 360 9 (pmN 360 9 (pmN 360 9 (invN 360 9 (RG.getD i (pidn 360 9))) (awN RG zWord))
      (RG.getD i (pidn 360 9))) (invN 360 9 (awN RG zWord))

end CertificateChecks.KernelAE6C2

end
