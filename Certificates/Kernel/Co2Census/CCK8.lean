module

public import Certificates.Kernel.Co2Census.CCDefs
public import Certificates.Kernel.Co2Census.HPData
public import Certificates.Kernel.Co2Census.CCData
public import Certificates.Kernel.Co2Census.S0Data
public import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2Census

theorem K8_gens : (List.range 6).all (genOKC QKt K8Gt K8GRt K8GIt 0 144) = true := by
  decide +kernel

theorem K8Z_tree : ∀ i < 112, treeK (conjStep K8GRt K8GIt) 6 112 K8ZPt K8ZXt i = true := by
  kc_cover 112

theorem K8Z_roots : (List.range 24).all (rootOKC K8ZPt K8ZXt K8Zrt 112) = true := by
  decide +kernel

theorem K8Z_cover : ∀ i < 112, coverRootK K8ZXt K8Zrt 24 i = true := by
  kc_cover 112

theorem K8Z_pos : ∀ j < 5104,
    posK (fun x => Nat.beq (mulV x (SK 144)) (mulV (SK 144) x)) LPt K8ZPt K8Zct 112 j =
      true := by
  kc_cover 1024

theorem K8Z_total : totalC QKt K8ZXt K8Zrt 112 2 24 144 0 (mulV (SK 144) (QKt 0))
    (mulV (SK 0) (QKt 256)) true = 0 := by
  decide +kernel

theorem K8_fib : ∀ j < 32, fibOKC QKt K8Ft 0 144 j = true := by
  kc_cover 32

theorem K8_rep : (repOKC (mulV (SK 144) (QKt 0)) (mulV (SK 0) (QKt 256)) &&
    Nat.beq (ceK QKt (mulV (SK 144) (QKt 0))) 16 &&
    Nat.beq (invEK QKt (mulV (SK 144) (QKt 0))) 32) = true := by
  decide +kernel

@[expose] def f1c (j : Nat) : Nat := [0, 26805, 2331, 1082, 144].getD j 0

theorem F1C_total : ((List.range 5).map fun j => rootCount LXt 5104 80 (Lrt j) *
    fcC QKt (f1c j) 0 0 IDP IDP false).sum = 178688 := by
  decide +kernel

theorem C26805_noroot :
    ∀ j < 23040, (!Nat.beq (mulV (C26805Pt j) (C26805Pt j)) (SK 26805)) = true := by
  kc_cover 2048

end CertificateChecks.KernelCo2Census
