module

public import Certificates.Data.Kernel.Misc.YamakiRepF
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.BfsK CFSG.KD.YamakiRepF
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def powF (x m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE (fun _ acc => MULF acc x) m

@[expose] noncomputable def invK (y u : Nat) : Bool :=
  bAnd(Nat.beq (MULF u u) ONE, bIf(Nat.beq u ONE, false, bIf(Nat.beq u y, false, true)))

@[expose] noncomputable def plK (x y k : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun _ ih u => bIf(invK y u, true, strictY (MULF u x) ih)) k

@[expose] noncomputable def powInvolK (y x : Nat) : Bool :=
  strictY (MULF ONE x) (plK x y 12)

@[expose] noncomputable def stepK (e z : Nat) : Nat := MULF (MULF (MULF e z) e) (powF z 11)

@[expose] noncomputable def good1K (y e₁ e₂ z : Nat) : Bool :=
  bIf(powInvolK y z, true, strictY (stepK e₁ z) fun s => bIf(powInvolK y s, true,
    strictY (stepK e₂ z) fun s' => powInvolK y s'))

@[expose] noncomputable def good2K (y e₁ e₂ z : Nat) : Bool :=
  bIf(good1K y e₁ e₂ z, true, strictY (stepK e₁ z) fun s => bIf(good1K y e₁ e₂ s, true,
    strictY (stepK e₂ z) fun s' => good1K y e₁ e₂ s'))

@[expose] noncomputable def closAt (y e₁ e₂ x : Nat) : Bool :=
  bIf(Nat.beq (MULF x y) (MULF y x),
    bIf(Nat.beq x ONE, true, bIf(Nat.beq x y, true, good2K y e₁ e₂ x)), true)

@[expose] noncomputable def closChunk (R : Nat → Nat) (o n y e₁ e₂ L q : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t =>
    bIf(Nat.blt t n, strictY (recX R o t) (closAt y e₁ e₂), true)

@[expose] noncomputable def centInvK (y e : Nat) : Bool :=
  bAnd(Nat.beq (MULF e y) (MULF y e), Nat.beq (MULF e e) ONE)

end CFSG.KD.OmegaSix

end
