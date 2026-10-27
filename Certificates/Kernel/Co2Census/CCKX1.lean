module

public import Certificates.Kernel.Co2Census.CCXDefs
public import Certificates.Kernel.Co2Census.HPData
public import Certificates.Kernel.Co2Census.CCData
public import CFSG.Certificates.Kernel.Common.Cover
public import Certificates.Kernel.Co2Census.CCDefs

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2Census CFSG.KC.Loop

@[expose] noncomputable def R1 : Nat := mulV (SK 26805) (QKt 0)

@[expose] noncomputable def hmin1OK (c : Nat) : Bool :=
  letB (X1Ht c) fun h => letB (fld21 h 1) fun len =>
    Nat.blt (fld21 h 0) 512 && certXOK QKt 2 h R1 len &&
      Nat.beq (certProd QKt 2 h (QKt (fld21 h 0)) len) (mulV (SK 0) (QKt 256))

theorem X1_D : dlK QKt R1 = (List.range 32).map X1Dt := by
  decide +kernel

theorem X1_abel : ∀ k < 1024, commK (QKt (X1Dt (k / 32))) (QKt (X1Dt (k % 32))) = true := by
  kc_cover 256

theorem X1_pts : ∀ j < 23040, (((List.range 32).any fun g => Nat.beq (X1Gdt g) j) ||
    (Nat.blt (X1Wt j) 32 && !commK (C26805Pt j) (QKt (X1Dt (X1Wt j))))) = true := by
  kc_cover 2048

theorem X1_good : ∀ k < 1024, (letB (C26805Pt (X1Gdt (k / 32))) fun s =>
    letB (QKt (X1Dt (k % 32))) fun d => Nat.blt (X1Gdt (k / 32)) 23040 && commK s d &&
      (letB (mulV s d) fun y => Nat.beq (mulV y y) IDP)) = true := by
  kc_cover 256

theorem X1_hmin : ∀ c < 31, hmin1OK c = true := by
  kc_cover 31

theorem X1_hcov : ∀ t < 32, (Nat.beq (X1Dt t) 0 ||
    (List.range 31).any fun c => Nat.beq (fld21 (X1Ht c) 0) (X1Dt t)) = true := by
  kc_cover 32

theorem X1_misc : ((letB (mulV (SK 225319) (QKt 0)) fun J => commK J R1 &&
    ((List.range 32).all fun t => commK J (QKt (X1Dt t))) && Nat.beq (invEK QKt J) 80) &&
    (letB (mulV (SK (fld21 (X1Tt 0) 1)) (QKt (fld21 (X1Tt 0) 0))) fun H =>
      Nat.blt (fld21 (X1Tt 0) 0) 512 &&
      Nat.beq (mulV H (mulV (mulV (SK 26805) (QKt 32)) (mulV (SK 0) (QKt 256)))) (mulV R1 H))) =
      true := by
  decide +kernel

end CertificateChecks.KernelCo2Census
