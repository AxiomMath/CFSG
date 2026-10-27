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

@[expose] noncomputable def R7 : Nat := mulV (SK 1082) (QKt 13)

@[expose] noncomputable def x7 (j : Nat) : Nat := mulV (C1082Pt j) (QKt (X7Lt j))

@[expose] def ZA7 : List (Nat × Nat) :=
  [(0, 0), (256, 0), (13, 1082), (269, 1082), (13, 156328), (269, 156328), (0, 1437869),
    (256, 1437869)]

@[expose] noncomputable def za7 (a : Nat) : Nat :=
  mulV (SK (ZA7.getD a (0, 0)).2) (QKt (ZA7.getD a (0, 0)).1)

@[expose] noncomputable def hmin7OK (c : Nat) : Bool :=
  letB (X7Ht c) fun h => letB (fld21 h 4) fun len =>
    letB (certProd QKt 5 h (QKt (fld21 h 0)) len) fun t =>
    Nat.blt (fld21 h 0) 512 && certXOK QKt 5 h R7 len &&
      (if fld21 h 1 = 0 then Nat.beq t (mulV (SK 0) (QKt 256)) else
        !Nat.beq t IDP && Nat.blt (fld21 h 2) 512 &&
          (letB (mulV (SK (fld21 h 3)) (QKt (fld21 h 2))) fun H =>
            Nat.beq (mulV H (mulV R7 t)) (mulV R7 H)))

theorem X7_D : dlK QKt R7 = (List.range 32).map X7Dt := by
  decide +kernel

theorem X7_abel : ∀ k < 1024, commK (QKt (X7Dt (k / 32))) (QKt (X7Dt (k % 32))) = true := by
  kc_cover 256

theorem X7_lift : ∀ j < 1536, (letB (x7 j) fun x => Nat.blt (X7Lt j) 512 && commK x R7 &&
    (((List.range 32).any fun g => Nat.beq (X7Gdt g) j) ||
      (Nat.blt (X7Wt j) 32 && !commK x (QKt (X7Dt (X7Wt j)))))) = true := by
  kc_cover 512

theorem X7_zd : ∀ t < 32, (Nat.beq (X7Dt t) 0 || Nat.beq (X7Dt t) 256 ||
    (Nat.blt (X7Zt t) 1536 && !commK (x7 (X7Zt t)) (QKt (X7Dt t)))) = true := by
  kc_cover 32

theorem X7_za : ∀ a < 8, (letB (za7 a) fun y => commK y R7 &&
    ((List.range 32).all fun t => commK y (QKt (X7Dt t))) &&
    ((List.range 1536).all fun j => commK y (x7 j)) &&
    ((List.range a).all fun b => !Nat.beq (za7 b) y)) = true := by
  kc_cover 1

theorem X7_hmin : ∀ c < 31, hmin7OK c = true := by
  kc_cover 31

theorem X7_hcov : ∀ t < 32, (Nat.beq (X7Dt t) 0 ||
    (List.range 31).any fun c => Nat.beq (fld21 (X7Ht c) 0) (X7Dt t)) = true := by
  kc_cover 32

end CertificateChecks.KernelCo2Census
