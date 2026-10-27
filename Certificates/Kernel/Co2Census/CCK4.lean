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

theorem K4_gens : (List.range 6).all (genOKC QKt K4Gt K4GRt K4GIt 2 2331) = true := by
  decide +kernel

theorem K4Z_tree : ∀ i < 368, treeK (conjStep K4GRt K4GIt) 6 368 K4ZPt K4ZXt i = true := by
  kc_cover 368

theorem K4Z_roots : (List.range 40).all (rootOKC K4ZPt K4ZXt K4Zrt 368) = true := by
  decide +kernel

theorem K4Z_cover : ∀ i < 368, coverRootK K4ZXt K4Zrt 40 i = true := by
  kc_cover 368

theorem K4Z_pos : ∀ j < 5104,
    posK (fun x => Nat.beq (mulV x (SK 2331)) (mulV (SK 2331) x)) LPt K4ZPt K4Zct 368 j =
      true := by
  kc_cover 1024

theorem K4Z_total : totalC QKt K4ZXt K4Zrt 368 6 40 2331 0 (mulV (SK 2331) (QKt 2))
    (mulV (SK 0) (QKt 256)) true = 192 := by
  decide +kernel

theorem K4R_tree : ∀ i < 48, treeK (conjStep K4GRt K4GIt) 6 48 K4RPt K4RXt i = true := by
  kc_cover 48

theorem K4R_roots : (List.range 7).all (rootOKC K4RPt K4RXt K4Rrt 48) = true := by
  decide +kernel

theorem K4R_cover : ∀ i < 48, coverRootK K4RXt K4Rrt 7 i = true := by
  kc_cover 48

theorem K4R_pos : ∀ j < 4608,
    posK (fun x => Nat.beq (mulV x x) (SK 2331)) C2331Pt K4RPt K4Rct 48 j = true := by
  kc_cover 1024

theorem K4R_total : totalC QKt K4RXt K4Rrt 48 1 7 2331 2331 (mulV (SK 2331) (QKt 2))
    (mulV (SK 2331) (QKt 2)) true = 128 := by
  decide +kernel

theorem K4_fib : ∀ j < 72, fibOKC QKt K4Ft 2 2331 j = true := by
  kc_cover 72

theorem K4_rep : (repOKC (mulV (SK 2331) (QKt 2)) (mulV (SK 0) (QKt 256)) &&
    Nat.beq (ceK QKt (mulV (SK 2331) (QKt 2))) 64 &&
    Nat.beq (invEK QKt (mulV (SK 2331) (QKt 2))) 80) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Census
