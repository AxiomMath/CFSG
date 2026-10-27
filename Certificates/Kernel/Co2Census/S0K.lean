module

public import Certificates.Kernel.Co2Census.S0Defs
public import Certificates.Kernel.Co2SmithS.Lets
public import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2Census CertificateChecks.KernelCo2SmithS

theorem L_tree : ∀ i < 5104, treeK stL 2 5104 LPt LXt i = true := by
  kc_cover 512

theorem L_clos : ∀ i < 5104, closK stL 2 5104 LPt LXt i = true := by
  kc_cover 512

@[expose] def s0Reps : List Nat := [26805, 2331, 1082, 144]

@[expose] def s0Sizes : List Nat := [1, 63, 315, 945, 3780]

theorem L_misc : (Nat.beq (ABt 0) (mulV (LT 2) IDP) && Nat.beq (ABt 1) (mulV (LT 3) IDP) &&
    Nat.beq (mulV (ABt 0) (ABIt 0)) IDP && Nat.beq (mulV (ABt 1) (ABIt 1)) IDP &&
    Nat.beq (Lrt 0) 0 && Nat.beq (LPt 0) IDP &&
    (List.range 5).all (fun j => Nat.blt (Lrt j) 5104 && Nat.beq (rtOf LXt (Lrt j)) (Lrt j) &&
      Nat.beq (rootCount LXt 5104 80 (Lrt j)) (s0Sizes.getD j 0)) &&
    (List.range 4).all fun j => Nat.beq (LPt (Lrt (j + 1))) (SK (s0Reps.getD j 0)) &&
      Nat.beq (mulV (LPt (Lrt (j + 1))) (LPt (Lrt (j + 1)))) IDP) = true := by
  decide +kernel

theorem ABI_lt : (Nat.blt (ABIt 0) (2 ^ 484) && Nat.blt (ABIt 1) (2 ^ 484)) = true := by
  decide +kernel

theorem L_roots : ∀ i < 5104,
    ((List.range 5).any fun j => Nat.beq (rtOf LXt i) (Lrt j)) = true := by
  kc_cover 1024

theorem T_tree : ∀ i < 512, treeK (rmStep TGRt) 9 512 TPt TXt i = true := by
  kc_cover 128

theorem T_clos : ∀ i < 512, closK (rmStep TGRt) 9 512 TPt TXt i = true := by
  kc_cover 128

theorem T_root : ∀ i < 512, Nat.beq (rtOf TXt i) 0 = true := by
  kc_cover 512

theorem T_misc : (Nat.beq (TPt 0) IDP &&
    (List.range 9).all fun l => Nat.beq (TGRt l) (SK (TGt l))) = true := by
  decide +kernel

theorem T_pos : ∀ j < 512,
    posK (fun x => Nat.beq (mulV x x) IDP) TPt LPt TPOSt 5104 j = true := by
  kc_cover 128

end CertificateChecks.KernelCo2Census
