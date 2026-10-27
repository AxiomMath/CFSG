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

@[expose] def syE (k : Nat) : Nat := [0, 2, 80].getD k 0

@[expose] noncomputable def RS (k : Nat) : Nat := mulV (SK 2331) (QKt (syE k))

@[expose] noncomputable def SL (k : Nat) : Nat → Nat :=
  if k = 0 then S0Lt else if k = 1 then S1Lt else S2Lt

@[expose] noncomputable def SGL (k : Nat) : Nat → Nat :=
  if k = 0 then S0GLt else if k = 1 then S1GLt else S2GLt

@[expose] noncomputable def SD (k : Nat) : Nat → Nat :=
  if k = 0 then S0Dt else if k = 1 then S1Dt else S2Dt

@[expose] noncomputable def SC (k : Nat) : Nat → Nat :=
  if k = 0 then S0Ct else if k = 1 then S1Ct else S2Ct

@[expose] def sDn (k : Nat) : Nat := [128, 64, 128].getD k 0

@[expose] noncomputable def xS (k j : Nat) : Nat := mulV (SyPt j) (QKt (SL k j))

@[expose] noncomputable def xSG (k l : Nat) : Nat := mulV (SyGRt l) (QKt (SGL k l))

@[expose] noncomputable def candOK (k c : Nat) : Bool :=
  letB (SC k c) fun w => letB (fld21 w 0) fun kind => letB (fld21 w 1) fun i =>
  letB (mulV (xS k (SyZt (c / sDn k))) (QKt (SD k (c % sDn k)))) fun y =>
    if kind = 0 then Nat.blt i 5 && !commK y (xSG k i)
    else if kind = 1 then Nat.blt i (sDn k) && !commK y (QKt (SD k i))
    else !Nat.beq (mulV y y) IDP || Nat.beq y IDP || Nat.beq y (mulV (SK 0) (QKt 256)) ||
      !Nat.beq (invEK QKt y) 32

theorem Sy_tree : ∀ i < 512, treeK (rmStep SyGRt) 5 512 SyPt SyXt i = true := by
  kc_cover 512

theorem Sy_clos : ∀ i < 512, closK (rmStep SyGRt) 5 512 SyPt SyXt i = true := by
  kc_cover 512

theorem Sy_root : ∀ i < 512, Nat.beq (rtOf SyXt i) 0 = true := by
  kc_cover 512

theorem Sy_misc : (Nat.beq (SyPt 0) IDP && (List.range 5).all fun l =>
    Nat.beq (SyGRt l) (SK (SyGt l))) = true := by
  decide +kernel

theorem Sy_cent : ∀ j < 512, (((List.range 4).any fun g => Nat.beq (SyZt g) j) ||
    (Nat.blt (SyWt j) 5 && !commK (SyPt j) (SyGRt (SyWt j)))) = true := by
  kc_cover 512

theorem Sy_zlt : (List.range 4).all (fun g => Nat.blt (SyZt g) 512) = true := by
  decide +kernel

theorem S_D : ∀ k < 3, (dlK QKt (RS k) == (List.range (sDn k)).map (SD k)) = true := by
  kc_cover 1

theorem S_lift : ∀ k < 3, ((List.range 512).all fun j => Nat.blt (SL k j) 512 &&
    commK (xS k j) (RS k)) = true := by
  kc_cover 1

theorem S_glift : ∀ k < 3, ((List.range 5).all fun l => Nat.blt (SGL k l) 512 &&
    commK (xSG k l) (RS k)) = true := by
  kc_cover 1

theorem S_cand : ∀ k < 3, ((List.range (4 * sDn k)).all (candOK k)) = true := by
  kc_cover 1

end CertificateChecks.KernelCo2Census
