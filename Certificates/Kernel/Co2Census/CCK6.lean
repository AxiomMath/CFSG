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

theorem K6_gens : (List.range 6).all (genOKC QKt K6Gt K6GRt K6GIt 0 1082) = true := by
  decide +kernel

theorem K6Z_tree : ∀ i < 240, treeK (conjStep K6GRt K6GIt) 6 240 K6ZPt K6ZXt i = true := by
  kc_cover 240

theorem K6Z_roots : (List.range 22).all (rootOKC K6ZPt K6ZXt K6Zrt 240) = true := by
  decide +kernel

theorem K6Z_cover : ∀ i < 240, coverRootK K6ZXt K6Zrt 22 i = true := by
  kc_cover 240

theorem K6Z_pos : ∀ j < 5104,
    posK (fun x => Nat.beq (mulV x (SK 1082)) (mulV (SK 1082) x)) LPt K6ZPt K6Zct 240 j =
      true := by
  kc_cover 1024

theorem K6Z_total : totalC QKt K6ZXt K6Zrt 240 4 22 1082 0 (mulV (SK 1082) (QKt 0))
    (mulV (SK 0) (QKt 256)) true = 0 := by
  decide +kernel

theorem K6R_tree : ∀ i < 64, treeK (conjStep K6GRt K6GIt) 6 64 K6RPt K6RXt i = true := by
  kc_cover 64

theorem K6R_roots : (List.range 3).all (rootOKC K6RPt K6RXt K6Rrt 64) = true := by
  decide +kernel

theorem K6R_cover : ∀ i < 64, coverRootK K6RXt K6Rrt 3 i = true := by
  kc_cover 64

theorem K6R_pos : ∀ j < 1536,
    posK (fun x => Nat.beq (mulV x x) (SK 1082)) C1082Pt K6RPt K6Rct 64 j = true := by
  kc_cover 768

theorem K6R_total : totalC QKt K6RXt K6Rrt 64 1 3 1082 1082 (mulV (SK 1082) (QKt 0))
    (mulV (SK 1082) (QKt 0)) true = 512 := by
  decide +kernel

theorem K6_fib : ∀ j < 16, fibOKC QKt K6Ft 0 1082 j = true := by
  kc_cover 16

theorem K6_rep : (repOKC (mulV (SK 1082) (QKt 0)) (mulV (SK 0) (QKt 256)) &&
    Nat.beq (ceK QKt (mulV (SK 1082) (QKt 0))) 32 &&
    Nat.beq (invEK QKt (mulV (SK 1082) (QKt 0))) 32) = true := by
  decide +kernel

theorem K7_gens : (List.range 6).all (genOKC QKt K7Gt K7GRt K7GIt 13 1082) = true := by
  decide +kernel

theorem K7Z_tree : ∀ i < 240, treeK (conjStep K7GRt K7GIt) 6 240 K7ZPt K7ZXt i = true := by
  kc_cover 240

theorem K7Z_roots : (List.range 22).all (rootOKC K7ZPt K7ZXt K7Zrt 240) = true := by
  decide +kernel

theorem K7Z_cover : ∀ i < 240, coverRootK K7ZXt K7Zrt 22 i = true := by
  kc_cover 240

theorem K7Z_pos : ∀ j < 5104,
    posK (fun x => Nat.beq (mulV x (SK 1082)) (mulV (SK 1082) x)) LPt K7ZPt K7Zct 240 j =
      true := by
  kc_cover 1024

theorem K7Z_total : totalC QKt K7ZXt K7Zrt 240 4 22 1082 0 (mulV (SK 1082) (QKt 13))
    (mulV (SK 0) (QKt 256)) true = 0 := by
  decide +kernel

theorem K7R_tree : ∀ i < 64, treeK (conjStep K7GRt K7GIt) 6 64 K7RPt K7RXt i = true := by
  kc_cover 64

theorem K7R_roots : (List.range 3).all (rootOKC K7RPt K7RXt K7Rrt 64) = true := by
  decide +kernel

theorem K7R_cover : ∀ i < 64, coverRootK K7RXt K7Rrt 3 i = true := by
  kc_cover 64

theorem K7R_pos : ∀ j < 1536,
    posK (fun x => Nat.beq (mulV x x) (SK 1082)) C1082Pt K7RPt K7Rct 64 j = true := by
  kc_cover 768

theorem K7R_total : totalC QKt K7RXt K7Rrt 64 1 3 1082 1082 (mulV (SK 1082) (QKt 13))
    (mulV (SK 1082) (QKt 13)) true = 0 := by
  decide +kernel

theorem K7_fib : ∀ j < 16, fibOKC QKt K7Ft 13 1082 j = true := by
  kc_cover 16

theorem K7_rep : (repOKC (mulV (SK 1082) (QKt 13)) (mulV (SK 0) (QKt 256)) &&
    Nat.beq (ceK QKt (mulV (SK 1082) (QKt 13))) 32 &&
    Nat.beq (invEK QKt (mulV (SK 1082) (QKt 13))) 32) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Census
