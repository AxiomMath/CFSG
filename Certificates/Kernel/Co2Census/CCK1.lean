module

public import Certificates.Kernel.Co2Census.CCDefs
public import Certificates.Kernel.Co2Census.HPData
public import Certificates.Kernel.Co2Census.CCData
public import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2Census

theorem K1_gens : (List.range 6).all (genOKC QKt K1Gt K1GRt K1GIt 0 26805) = true := by
  decide +kernel

theorem K1Z_tree : ∀ i < 752, treeK (conjStep K1GRt K1GIt) 6 752 K1ZPt K1ZXt i = true := by
  kc_cover 376

theorem K1Z_roots : (List.range 11).all (rootOKC K1ZPt K1ZXt K1Zrt 752) = true := by
  decide +kernel

theorem K1Z_cover : ∀ i < 752, coverRootK K1ZXt K1Zrt 11 i = true := by
  kc_cover 752

theorem K1Z_pos : ∀ j < 5104,
    posK (fun x => Nat.beq (mulV x (SK 26805)) (mulV (SK 26805) x)) LPt K1ZPt K1Zct 752 j =
      true := by
  kc_cover 1024

theorem K1Z_total : totalC QKt K1ZXt K1Zrt 752 12 11 26805 0 (mulV (SK 26805) (QKt 0))
    (mulV (SK 0) (QKt 256)) true = 0 := by
  decide +kernel

theorem K1_fib : ∀ j < 16, fibOKC QKt K1Ft 0 26805 j = true := by
  kc_cover 16

theorem K1_rep : (repOKC (mulV (SK 26805) (QKt 0)) (mulV (SK 0) (QKt 256)) &&
    Nat.beq (ceK QKt (mulV (SK 26805) (QKt 0))) 32 &&
    Nat.beq (invEK QKt (mulV (SK 26805) (QKt 0))) 32) = true := by
  decide +kernel

theorem K2_gens : (List.range 6).all (genOKC QKt K2Gt K2GRt K2GIt 32 26805) = true := by
  decide +kernel

theorem K2Z_tree : ∀ i < 752, treeK (conjStep K2GRt K2GIt) 6 752 K2ZPt K2ZXt i = true := by
  kc_cover 376

theorem K2Z_roots : (List.range 11).all (rootOKC K2ZPt K2ZXt K2Zrt 752) = true := by
  decide +kernel

theorem K2Z_cover : ∀ i < 752, coverRootK K2ZXt K2Zrt 11 i = true := by
  kc_cover 752

theorem K2Z_pos : ∀ j < 5104,
    posK (fun x => Nat.beq (mulV x (SK 26805)) (mulV (SK 26805) x)) LPt K2ZPt K2Zct 752 j =
      true := by
  kc_cover 1024

theorem K2Z_total : totalC QKt K2ZXt K2Zrt 752 12 11 26805 0 (mulV (SK 26805) (QKt 32))
    (mulV (SK 0) (QKt 256)) true = 0 := by
  decide +kernel

theorem K2_fib : ∀ j < 16, fibOKC QKt K2Ft 32 26805 j = true := by
  kc_cover 16

theorem K2_rep : (repOKC (mulV (SK 26805) (QKt 32)) (mulV (SK 0) (QKt 256)) &&
    Nat.beq (ceK QKt (mulV (SK 26805) (QKt 32))) 32 &&
    Nat.beq (invEK QKt (mulV (SK 26805) (QKt 32))) 32) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Census
