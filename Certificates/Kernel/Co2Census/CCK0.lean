module

public import Certificates.Kernel.Co2Census.CCDefs
public import Certificates.Kernel.Co2Census.HPData
public import Certificates.Kernel.Co2Census.CCData
public import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2Census

theorem K0_gens : (List.range 6).all (genOKC QKt K0Gt K0GRt K0GIt 1 0) = true := by
  decide +kernel

theorem K0Z_tree : ∀ i < 5104, treeK (conjStep K0GRt K0GIt) 6 5104 K0ZPt K0ZXt i = true := by
  kc_cover 512

theorem K0Z_roots : (List.range 18).all (rootOKC K0ZPt K0ZXt K0Zrt 5104) = true := by
  decide +kernel

theorem K0Z_cover : ∀ i < 5104, coverRootK K0ZXt K0Zrt 18 i = true := by
  kc_cover 1024

theorem K0Z_pos : ∀ j < 5104,
    posK (fun x => Nat.beq (mulV x (SK 0)) (mulV (SK 0) x)) LPt K0ZPt K0Zct 5104 j = true := by
  kc_cover 1024

theorem K0Z_total : totalC QKt K0ZXt K0Zrt 5104 80 18 0 0 (mulV (SK 0) (QKt 1))
    (mulV (SK 0) (QKt 256)) true = 1792 := by
  decide +kernel

theorem K0R_total : totalC QKt K0ZXt K0Zrt 5104 80 18 0 0 (mulV (SK 0) (QKt 1))
    (mulV (SK 0) (QKt 1)) true = 5376 := by
  decide +kernel

theorem K0_fib : ∀ j < 270, fibOKC QKt K0Ft 1 0 j = true := by
  kc_cover 64

theorem K0_rep : (repOKC (mulV (SK 0) (QKt 1)) (mulV (SK 0) (QKt 256)) && Nat.beq (ceK QKt (mulV (SK 0) (QKt 1))) 256 &&
    Nat.beq (invEK QKt (mulV (SK 0) (QKt 1))) 272) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Census
