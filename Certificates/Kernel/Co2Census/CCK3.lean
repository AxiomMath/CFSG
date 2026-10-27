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

theorem K3_gens : (List.range 6).all (genOKC QKt K3Gt K3GRt K3GIt 0 2331) = true := by
  decide +kernel

theorem K3Z_tree : ∀ i < 368, treeK (conjStep K3GRt K3GIt) 6 368 K3ZPt K3ZXt i = true := by
  kc_cover 368

theorem K3Z_roots : (List.range 14).all (rootOKC K3ZPt K3ZXt K3Zrt 368) = true := by
  decide +kernel

theorem K3Z_cover : ∀ i < 368, coverRootK K3ZXt K3Zrt 14 i = true := by
  kc_cover 368

theorem K3Z_pos : ∀ j < 5104,
    posK (fun x => Nat.beq (mulV x (SK 2331)) (mulV (SK 2331) x)) LPt K3ZPt K3Zct 368 j =
      true := by
  kc_cover 1024

theorem K3Z_total : totalC QKt K3ZXt K3Zrt 368 6 14 2331 0 (mulV (SK 2331) (QKt 0))
    (mulV (SK 0) (QKt 256)) true = 384 := by
  decide +kernel

theorem K3R_tree : ∀ i < 48, treeK (conjStep K3GRt K3GIt) 6 48 K3RPt K3RXt i = true := by
  kc_cover 48

theorem K3R_roots : (List.range 2).all (rootOKC K3RPt K3RXt K3Rrt 48) = true := by
  decide +kernel

theorem K3R_cover : ∀ i < 48, coverRootK K3RXt K3Rrt 2 i = true := by
  kc_cover 48

theorem K3R_pos : ∀ j < 4608,
    posK (fun x => Nat.beq (mulV x x) (SK 2331)) C2331Pt K3RPt K3Rct 48 j = true := by
  kc_cover 1024

theorem K3R_total : totalC QKt K3RXt K3Rrt 48 1 2 2331 2331 (mulV (SK 2331) (QKt 0))
    (mulV (SK 2331) (QKt 0)) true = 1152 := by
  decide +kernel

theorem K3_fib : ∀ j < 4, fibOKC QKt K3Ft 0 2331 j = true := by
  kc_cover 4

theorem K3_rep : (repOKC (mulV (SK 2331) (QKt 0)) (mulV (SK 0) (QKt 256)) &&
    Nat.beq (ceK QKt (mulV (SK 2331) (QKt 0))) 128 &&
    Nat.beq (invEK QKt (mulV (SK 2331) (QKt 0))) 80) = true := by
  decide +kernel

theorem K5_gens : (List.range 6).all (genOKC QKt K5Gt K5GRt K5GIt 80 2331) = true := by
  decide +kernel

theorem K5Z_tree : ∀ i < 368, treeK (conjStep K5GRt K5GIt) 6 368 K5ZPt K5ZXt i = true := by
  kc_cover 368

theorem K5Z_roots : (List.range 14).all (rootOKC K5ZPt K5ZXt K5Zrt 368) = true := by
  decide +kernel

theorem K5Z_cover : ∀ i < 368, coverRootK K5ZXt K5Zrt 14 i = true := by
  kc_cover 368

theorem K5Z_pos : ∀ j < 5104,
    posK (fun x => Nat.beq (mulV x (SK 2331)) (mulV (SK 2331) x)) LPt K5ZPt K5Zct 368 j =
      true := by
  kc_cover 1024

theorem K5Z_total : totalC QKt K5ZXt K5Zrt 368 6 14 2331 0 (mulV (SK 2331) (QKt 80))
    (mulV (SK 0) (QKt 256)) true = 384 := by
  decide +kernel

theorem K5R_tree : ∀ i < 48, treeK (conjStep K5GRt K5GIt) 6 48 K5RPt K5RXt i = true := by
  kc_cover 48

theorem K5R_roots : (List.range 2).all (rootOKC K5RPt K5RXt K5Rrt 48) = true := by
  decide +kernel

theorem K5R_cover : ∀ i < 48, coverRootK K5RXt K5Rrt 2 i = true := by
  kc_cover 48

theorem K5R_pos : ∀ j < 4608,
    posK (fun x => Nat.beq (mulV x x) (SK 2331)) C2331Pt K5RPt K5Rct 48 j = true := by
  kc_cover 1024

theorem K5R_total : totalC QKt K5RXt K5Rrt 48 1 2 2331 2331 (mulV (SK 2331) (QKt 80))
    (mulV (SK 2331) (QKt 80)) true = 384 := by
  decide +kernel

theorem K5_fib : ∀ j < 4, fibOKC QKt K5Ft 80 2331 j = true := by
  kc_cover 4

theorem K5_rep : (repOKC (mulV (SK 2331) (QKt 80)) (mulV (SK 0) (QKt 256)) &&
    Nat.beq (ceK QKt (mulV (SK 2331) (QKt 80))) 128 &&
    Nat.beq (invEK QKt (mulV (SK 2331) (QKt 80))) 80) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Census
