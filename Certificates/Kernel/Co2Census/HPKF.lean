module

public import Certificates.Kernel.Co2Census.HPDefs
public import Certificates.Kernel.Co2Census.HPData
public import Certificates.Kernel.Co2SmithS.ElK
public import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2Census

@[expose] def f1n (j : Nat) : Nat := [0, 26805, 2331, 1082, 144].getD j 0

@[expose] def hpRepE (i : Nat) : Nat := [1, 0, 2, 0].getD i 0

@[expose] def hpRepN (i : Nat) : Nat := [0, 2331, 2331, 144].getD i 0

theorem Q_ok : ∀ e < 512, Nat.beq (QKt e) (KernelCo2SmithS.nfS (e / 256) (e % 256)) = true := by
  kc_cover 128

theorem F1_ok : ((List.range 5).all fun j => fcOK (f1n j) 0 0 false) = true := by
  decide +kernel

theorem F1_total : ((List.range 5).map fun j => rootCount LXt 5104 80 (Lrt j) *
    fcK QKt (f1n j) 0 0 (mulV (SK 0) (QKt 0)) (mulV (SK 0) (QKt 0)) false).sum = 146432 := by
  decide +kernel

theorem F1_misc : (Nat.beq (SK 0) IDP && Nat.beq (SK 1) (ABt 0) && Nat.beq (SK 2) (ABt 1) &&
    (List.range 5).map Lrt == [0, 1, 64, 379, 1324] && Nat.blt Z0 (2 ^ 484) &&
    Nat.beq (QKt 0) IDP && Nat.beq (QKt 256) Z0) = true := by
  decide +kernel

@[expose] noncomputable def repOK (i : Nat) : Bool :=
  letB (hpRepN i) fun nr => letB (mulV (SK nr) (QKt (hpRepE i))) fun RR =>
    Nat.blt (kSq nr 0) 2 && nzV (spinMV 0 v0) &&
      Nat.beq (mulV (SK nr) (SK nr)) IDP &&
      Nat.beq (mulV RR RR) (twistK (kSq nr 0) IDP) &&
      (!Nat.beq (SK nr) IDP || (!Nat.beq RR IDP && !Nat.beq RR Z0))

theorem rep_ok : (List.range 4).all repOK = true := by
  decide +kernel

end CertificateChecks.KernelCo2Census
