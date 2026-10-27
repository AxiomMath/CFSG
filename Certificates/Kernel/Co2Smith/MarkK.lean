module

public import Certificates.Data.Kernel.Co2Smith.Mark
public import Certificates.Kernel.Co2Smith.LettersData
public import CFSG.Sporadic.Co2Smith.GlC0MarkInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def reflK : List Nat := (List.range 36).map fun i => wK LP (glMkRWord i)

theorem c0_k : c0K LP FM (wK LP [12]) (wK LP [0]) reflK glWit0 glWit1 glWit2 = true := by
  decide +kernel

end CertificateChecks.KernelCo2Smith
