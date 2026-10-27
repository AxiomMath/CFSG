module

public import Certificates.Kernel.Co2Census.HPDefs
public import Certificates.Kernel.Co2Census.HPData
public import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2Census

theorem H1_gens : (List.range 6).all (genOK QKt H1Gt H1GRt H1GIt 0 2331) = true := by
  decide +kernel

theorem H1Z_tree : ∀ i < 368, treeK (conjStep H1GRt H1GIt) 6 368 H1ZPt H1ZXt i = true := by
  kc_cover 128

theorem H1Z_roots : (List.range 14).all (rootOK H1ZPt H1ZXt H1Zrt 368 2331 0 true) = true := by
  decide +kernel

theorem H1Z_cover : ∀ i < 368, coverRootK H1ZXt H1Zrt 14 i = true := by
  kc_cover 368

theorem H1Z_pos : ∀ j < 5104,
    posK (fun x => Nat.beq (mulV x (SK 2331)) (mulV (SK 2331) x)) LPt H1ZPt H1Zct 368 j = true := by
  kc_cover 1024

theorem H1Z_total : totalK QKt H1ZXt H1Zrt 368 6 14 2331 0 (mulV (SK 2331) (QKt 0))
    (mulV (SK 0) (QKt 256)) true = 1152 := by
  decide +kernel

theorem H1R_tree : ∀ i < 48, treeK (conjStep H1GRt H1GIt) 6 48 H1RPt H1RXt i = true := by
  kc_cover 48

theorem H1R_roots : (List.range 4).all (rootOK H1RPt H1RXt H1Rrt 48 2331 2331 true) = true := by
  decide +kernel

theorem H1R_cover : ∀ i < 48, coverRootK H1RXt H1Rrt 4 i = true := by
  kc_cover 48

theorem H1R_pos : ∀ j < 4608,
    posK (fun x => Nat.beq (mulV x x) (SK 2331)) C2331Pt H1RPt H1Rct 48 j = true := by
  kc_cover 1024

theorem H1R_total : totalK QKt H1RXt H1Rrt 48 1 4 2331 2331 (mulV (SK 2331) (QKt 0))
    (mulV (SK 2331) (QKt 0)) true = 768 := by
  decide +kernel

theorem H1_fib : (List.range 8).all (fibOK QKt H1Ft 0 2331) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Census
