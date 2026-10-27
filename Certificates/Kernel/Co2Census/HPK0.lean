module

public import Certificates.Kernel.Co2Census.HPDefs
public import Certificates.Kernel.Co2Census.HPData
public import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2Census

theorem H0_gens : (List.range 6).all (genOK QKt H0Gt H0GRt H0GIt 1 0) = true := by
  decide +kernel

theorem H0Z_tree : ∀ i < 5104, treeK (conjStep H0GRt H0GIt) 6 5104 H0ZPt H0ZXt i = true := by
  kc_cover 512

theorem H0Z_roots : (List.range 18).all (rootOK H0ZPt H0ZXt H0Zrt 5104 0 0 true) = true := by
  decide +kernel

theorem H0Z_cover : ∀ i < 5104, coverRootK H0ZXt H0Zrt 18 i = true := by
  kc_cover 1024

theorem H0Z_pos : ∀ j < 5104,
    posK (fun x => Nat.beq (mulV x (SK 0)) (mulV (SK 0) x)) LPt H0ZPt H0Zct 5104 j = true := by
  kc_cover 1024

theorem H0Z_total : totalK QKt H0ZXt H0Zrt 5104 80 18 0 0 (mulV (SK 0) (QKt 1))
    (mulV (SK 0) (QKt 256)) true = 5376 := by
  decide +kernel

theorem H0R_total : totalK QKt H0ZXt H0Zrt 5104 80 18 0 0 (mulV (SK 0) (QKt 1))
    (mulV (SK 0) (QKt 1)) true = 5376 := by
  decide +kernel

theorem H0_fib : ∀ j < 270, fibOK QKt H0Ft 1 0 j = true := by
  kc_cover 64

end CertificateChecks.KernelCo2Census
