module

public import Certificates.Kernel.Co2Census.HPDefs
public import Certificates.Kernel.Co2Census.HPData
public import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2Census

theorem H3_gens : (List.range 6).all (genOK QKt H3Gt H3GRt H3GIt 0 144) = true := by
  decide +kernel

theorem H3Z_tree : ∀ i < 112, treeK (conjStep H3GRt H3GIt) 6 112 H3ZPt H3ZXt i = true := by
  kc_cover 112

theorem H3Z_roots : (List.range 24).all (rootOK H3ZPt H3ZXt H3Zrt 112 144 0 true) = true := by
  decide +kernel

theorem H3Z_cover : ∀ i < 112, coverRootK H3ZXt H3Zrt 24 i = true := by
  kc_cover 112

theorem H3Z_pos : ∀ j < 5104,
    posK (fun x => Nat.beq (mulV x (SK 144)) (mulV (SK 144) x)) LPt H3ZPt H3Zct 112 j = true := by
  kc_cover 1024

theorem H3Z_total : totalK QKt H3ZXt H3Zrt 112 2 24 144 0 (mulV (SK 144) (QKt 0))
    (mulV (SK 0) (QKt 256)) true = 96 := by
  decide +kernel

theorem C144_noroot : ∀ j < 384, (!Nat.beq (mulV (C144Pt j) (C144Pt j)) (SK 144)) = true := by
  kc_cover 384

theorem H3_fib : (List.range 32).all (fibOK QKt H3Ft 0 144) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Census
