module

public import Certificates.Data.Kernel.Misc.BfsKW
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KD.BfsKW

open CFSG.KD.BfsK

@[expose] noncomputable def strictW (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def fldW (r f : Nat) : Nat :=
  Nat.land (Nat.shiftRight r (Nat.add 64 (Nat.mul 32 f))) M32

@[expose] noncomputable def walkLW (R : Nat → Nat) (o : Nat) (P : Nat → Nat)
    (B : Nat → Nat → Nat → Nat → Nat → Bool) (b m : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun l ih rn qn => strictW (R (Nat.add o (Nat.add b l))) fun r =>
      strictW (R (Nat.add o (P r))) fun q => bAnd(B (Nat.add b l) r rn q qn, ih r q)) m

@[expose] noncomputable def walkW (R : Nat → Nat) (o : Nat) (P : Nat → Nat)
    (B : Nat → Nat → Nat → Nat → Nat → Bool) (b m : Nat) : Bool :=
  strictW (R (Nat.add o (Nat.add b m))) fun rn => strictW (R (Nat.add o (P rn))) fun qn =>
    walkLW R o P B b m rn qn

@[expose] noncomputable def buildAtW (st : Nat → Nat → Nat) (n k i r rn q _qn : Nat) : Bool :=
  bIf(Nat.blt (Nat.succ i) n, strictW (fldW r 1) fun s =>
    Nat.ble (fldW r 0) i && Nat.blt s k && Nat.beq (Nat.land rn M64) (st (Nat.land q M64) s),
    true)

@[expose] noncomputable def sortAtW (R : Nat → Nat) (o n i r rn q qn : Nat) : Bool :=
  bIf(Nat.blt i n, strictW (R (Nat.add o (fldW r 3))) fun s =>
    Nat.blt (fldW r 2) n && Nat.blt (fldW r 3) n && Nat.beq (fldW q 3) i &&
      Nat.beq (fldW s 2) i &&
      cond (Nat.blt (Nat.succ i) n) (Nat.blt (Nat.land q M64) (Nat.land qn M64)) true,
    true)

@[expose] noncomputable def buildSlW (R : Nat → Nat) (st : Nat → Nat → Nat) (o n k j : Nat) :
    Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun c ih => bAnd(walkW R o (fun r => fldW r 0)
    (buildAtW st n k) (Nat.add (Nat.mul j 1024) (Nat.mul c 64)) 64, ih)) 16

@[expose] noncomputable def sortSlW (R : Nat → Nat) (o n j : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun c ih => bAnd(walkW R o (fun r => fldW r 2)
    (sortAtW R o n) (Nat.add (Nat.mul j 1024) (Nat.mul c 64)) 64, ih)) 16

end CFSG.KD.BfsKW

end
