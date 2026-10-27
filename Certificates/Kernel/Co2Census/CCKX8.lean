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

@[expose] noncomputable def R8 : Nat := mulV (SK 144) (QKt 0)

@[expose] def D8 : List Nat :=
  [0, 13, 118, 123, 183, 186, 193, 204, 256, 269, 374, 379, 439, 442, 449, 460]

@[expose] noncomputable def x8 (j : Nat) : Nat := mulV (C144Pt j) (QKt (X8Lt j))

@[expose] noncomputable def u8 (k : Nat) : Nat := mulV (x8 (k / 16)) (QKt (D8.getD (k % 16) 0))

theorem X8_D : dlK QKt R8 = D8 := by
  decide +kernel

theorem X8_lift : ∀ j < 384, (Nat.blt (X8Lt j) 512 && commK (x8 j) R8) = true := by
  kc_cover 384

theorem X8_sq : ∀ k < 6144, (letB (u8 k) fun u => Nat.blt (X8Gt k) 169 &&
    Nat.beq (mulV u u) (X8Vt (X8Gt k))) = true := by
  kc_cover 512

theorem X8_inc : ∀ g < 168, Nat.blt (X8Vt g) (X8Vt (g + 1)) = true := by
  kc_cover 168

theorem X8_cnt : ∀ g < 169, (Nat.beq g (X8wt 0) ||
    !Nat.beq ((List.range 6144).filter fun k => Nat.beq (X8Gt k) g).length 384) = true := by
  kc_cover 13

theorem X8_misc : (Nat.blt (X8wt 0) 169 && Nat.beq (X8Vt (X8wt 0)) (QKt 269) &&
    ((List.range 6144).filter fun k => Nat.beq (X8Gt k) (X8wt 0)).length == 384 &&
    commK (QKt 269) R8 && !Nat.beq (QKt 269) IDP &&
    (letB (mulV (SK (fld21 (X8Ht 0) 1)) (QKt (fld21 (X8Ht 0) 0))) fun H =>
      Nat.blt (fld21 (X8Ht 0) 0) 512 && Nat.beq (mulV H (mulV R8 (QKt 269))) (mulV R8 H))) =
      true := by
  decide +kernel

end CertificateChecks.KernelCo2Census
