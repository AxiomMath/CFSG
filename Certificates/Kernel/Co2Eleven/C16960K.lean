module

public import Certificates.Kernel.Co2Eleven.Data7
public import Certificates.Kernel.SporSch.Co2M.Seeds
public import Certificates.Data.Kernel.Co2Eleven
public import CFSG.Certificates.Kernel.Spor.SlpMatSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Eleven

open CFSG.KC.Co2Eleven CertificateChecks.KernelSporSch.Co2M

@[expose] noncomputable def wcK7 : List (List Nat) := chunkK WN7 WF7

@[expose] noncomputable def wsK7 : List (List Int) := wcK7.map CFSG.KC.SlpM.decW

@[expose] def idW7 : List Nat := [4, 313, 314, 315, 316, 317, 318, 319]

@[expose] def chainW7 : List Nat :=
  [0, 1, 50, 56, 62, 108, 114, 120, 166, 172, 178, 184, 190, 196, 242, 248, 254, 300, 306, 312]

theorem letters7_k : lettersK (AP 0) (AP 1) WV7 WVI7 wsK7 = true := by decide +kernel

theorem levels7_k : levelsK WV7 WVI7 R7 chainW7 3 4 7 SZ7 = true := by decide +kernel

theorem count7_k : countK WV7 WVI7 R7 chainW7 3 4 7 56 SZ7 = true := by decide +kernel

theorem misc7_k : miscK WV7 wsK7 chainW7 3 4 7 7 SZ7 = true := by decide +kernel

theorem cent7_k : centK WV7 wsK7 idW7 3 4 7 = true := by decide +kernel

end CertificateChecks.KernelCo2Eleven

end
