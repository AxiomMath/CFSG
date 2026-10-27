module

public import Certificates.Kernel.Co2Smith.RefData
public import Certificates.Kernel.Co2Smith.ArcData
public import Certificates.Data.Kernel.Co2Smith.RefineA

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2SmithR CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def c0Arcs : List Nat := [AP 0, AP 1]

@[expose] noncomputable def czArcs : List Nat := [AP 0, AP 1, AP 2]

theorem c0_cls0 : classA 2300 RS c0Arcs [] 3 80 (glWit0.map (·.1)) = true := by decide +kernel
theorem c0_cls1 : classA 2300 RS c0Arcs [80] 3 1 (glWit1.map (·.1)) = true := by decide +kernel
theorem c0_cls2 : classA 2300 RS c0Arcs [80, 1] 3 0 (glWit2.map (·.1)) = true := by decide +kernel
theorem c0_extra1 : classA 2300 RS c0Arcs [80] 3 1172 (glWit0Pts 1) = true := by decide +kernel
theorem c0_extra2 : classA 2300 RS c0Arcs [80] 3 1348 (glWit0Pts 2) = true := by decide +kernel

theorem cz_cls0 : classA 2300 RS czArcs [] 3 80 (glWitZ0.map (·.1)) = true := by decide +kernel
theorem cz_cls1 : classA 2300 RS czArcs [80] 3 1 (glWitZ1.map (·.1)) = true := by decide +kernel
theorem cz_cls2 : classA 2300 RS czArcs [80, 1] 3 0 (glWitZ2.map (·.1)) = true := by
  decide +kernel

theorem c0_sing0 : singA 2300 RS c0Arcs [80, 1, 0] 3 0 256 = true := by decide +kernel
theorem c0_sing1 : singA 2300 RS c0Arcs [80, 1, 0] 3 256 256 = true := by decide +kernel
theorem c0_sing2 : singA 2300 RS c0Arcs [80, 1, 0] 3 512 256 = true := by decide +kernel
theorem c0_sing3 : singA 2300 RS c0Arcs [80, 1, 0] 3 768 256 = true := by decide +kernel
theorem c0_sing4 : singA 2300 RS c0Arcs [80, 1, 0] 3 1024 256 = true := by decide +kernel
theorem c0_sing5 : singA 2300 RS c0Arcs [80, 1, 0] 3 1280 256 = true := by decide +kernel
theorem c0_sing6 : singA 2300 RS c0Arcs [80, 1, 0] 3 1536 256 = true := by decide +kernel
theorem c0_sing7 : singA 2300 RS c0Arcs [80, 1, 0] 3 1792 256 = true := by decide +kernel
theorem c0_sing8 : singA 2300 RS c0Arcs [80, 1, 0] 3 2048 252 = true := by decide +kernel

theorem cz_sing0 : singA 2300 RS czArcs [80, 1, 0] 3 0 256 = true := by decide +kernel
theorem cz_sing1 : singA 2300 RS czArcs [80, 1, 0] 3 256 256 = true := by decide +kernel
theorem cz_sing2 : singA 2300 RS czArcs [80, 1, 0] 3 512 256 = true := by decide +kernel
theorem cz_sing3 : singA 2300 RS czArcs [80, 1, 0] 3 768 256 = true := by decide +kernel
theorem cz_sing4 : singA 2300 RS czArcs [80, 1, 0] 3 1024 256 = true := by decide +kernel
theorem cz_sing5 : singA 2300 RS czArcs [80, 1, 0] 3 1280 256 = true := by decide +kernel
theorem cz_sing6 : singA 2300 RS czArcs [80, 1, 0] 3 1536 256 = true := by decide +kernel
theorem cz_sing7 : singA 2300 RS czArcs [80, 1, 0] 3 1792 256 = true := by decide +kernel
theorem cz_sing8 : singA 2300 RS czArcs [80, 1, 0] 3 2048 252 = true := by decide +kernel

end CertificateChecks.KernelCo2Smith

end
