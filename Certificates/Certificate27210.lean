module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24ModelHex
import CFSG.Certificates.Kernel.EvenSporG24Hex.Sound
import Certificates.Kernel.EvenSporG24Hex.Checks
import Certificates.Kernel.EvenSporG24Hex.HexA
import Certificates.Kernel.EvenSporG24Hex.HexB

public section

open CFSG.EvenSporadicStandard.G24Model CFSG.KC.EvenSporG24Hex CertificateChecks.KernelG24Hex

namespace CertificateChecks.Batch27210

open CFSG.EvenSporadicStandard.G24Model CFSG.KC.EvenSporG24Hex CertificateChecks.KernelG24Hex

private theorem hexAll : ∀ j < 16, hexJ D.U D.W D.GE D.PG D.LC j = true := by
  intro j hj
  interval_cases j
  exacts [hexF0, hexF1, hexF2, hexF3, hexF4, hexF5, hexF6, hexF7, hexF8, hexF9, hexF10, hexF11,
    hexF12, hexF13, hexF14, hexF15]

theorem hex_0 : hexOK = true :=
  hexOK_of EvenSporG24.tbl_eq dataOK_true linesOK_true keysOK_true lcOK_true hexAll

end CertificateChecks.Batch27210

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.G24Model in
theorem certificate27210 : hexOK = true := CertificateChecks.Batch27210.hex_0

end Certificates
