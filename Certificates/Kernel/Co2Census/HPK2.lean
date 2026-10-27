module

public import Certificates.Kernel.Co2Census.HPDefs
public import Certificates.Kernel.Co2Census.HPData
public import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2Census

theorem H2_gens : (List.range 6).all (genOK QKt H2Gt H2GRt H2GIt 2 2331) = true := by
  decide +kernel

theorem H2Z_tree : ∀ i < 368, treeK (conjStep H2GRt H2GIt) 6 368 H2ZPt H2ZXt i = true := by
  kc_cover 128

theorem H2Z_roots : (List.range 40).all (rootOK H2ZPt H2ZXt H2Zrt 368 2331 0 true) = true := by
  decide +kernel

theorem H2Z_cover : ∀ i < 368, coverRootK H2ZXt H2Zrt 40 i = true := by
  kc_cover 368

theorem H2Z_pos : ∀ j < 5104,
    posK (fun x => Nat.beq (mulV x (SK 2331)) (mulV (SK 2331) x)) LPt H2ZPt H2Zct 368 j = true := by
  kc_cover 1024

theorem H2Z_total : totalK QKt H2ZXt H2Zrt 368 6 40 2331 0 (mulV (SK 2331) (QKt 2))
    (mulV (SK 0) (QKt 256)) true = 448 := by
  decide +kernel

theorem H2R_tree : ∀ i < 48, treeK (conjStep H2GRt H2GIt) 6 48 H2RPt H2RXt i = true := by
  kc_cover 48

theorem H2R_roots : (List.range 7).all (rootOK H2RPt H2RXt H2Rrt 48 2331 2331 true) = true := by
  decide +kernel

theorem H2R_cover : ∀ i < 48, coverRootK H2RXt H2Rrt 7 i = true := by
  kc_cover 48

theorem H2R_pos : ∀ j < 4608,
    posK (fun x => Nat.beq (mulV x x) (SK 2331)) C2331Pt H2RPt H2Rct 48 j = true := by
  kc_cover 1024

theorem H2R_total : totalK QKt H2RXt H2Rrt 48 1 7 2331 2331 (mulV (SK 2331) (QKt 2))
    (mulV (SK 2331) (QKt 2)) true = 128 := by
  decide +kernel

theorem H2_fib : (List.range 72).all (fibOK QKt H2Ft 2 2331) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Census
