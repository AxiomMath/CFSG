module

public import Certificates.Kernel.Co2Eleven.Data
public import Certificates.Kernel.SporSch.Co2M.Seeds
public import Certificates.Data.Kernel.Co2Eleven
public import CFSG.Certificates.Kernel.Spor.SlpMatSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Eleven

open CFSG.KC.Co2Eleven CertificateChecks.KernelSporSch.Co2M

@[expose] noncomputable def wcK : List (List Nat) := chunkK WN WF

@[expose] noncomputable def wsK : List (List Int) := wcK.map CFSG.KC.SlpM.decW

@[expose] def chainW : List Nat := [0, 1, 37, 40, 43, 46, 49, 52, 55, 58, 61, 64]

theorem letters_k : lettersK (AP 0) (AP 1) WV WVI wsK = true := by decide +kernel

theorem levels_k : levelsK WV WVI R chainW 33 34 7 SZ = true := by decide +kernel

theorem count_k : countK WV WVI R chainW 33 34 7 11 SZ = true := by decide +kernel

theorem misc_k : miscK WV wsK chainW 33 34 7 11 SZ = true := by decide +kernel

end CertificateChecks.KernelCo2Eleven

end
