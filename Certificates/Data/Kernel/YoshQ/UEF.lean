module

public import Certificates.Data.Kernel.YoshQ.Fast

public section

namespace CFSG.KC.YoshQ

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def memT (P M : Nat) (T : Nat → Nat) (t : Nat) : Bool :=
  strictB (hN P t) fun h => hasBit M h && eqN 16 5 (T h) t

@[expose] noncomputable def cInI (one c a ai b bi : Nat) : Bool :=
  strictB (pmN 16 5 (pmN 16 5 a b) (pmN 16 5 ai bi)) fun t => eqN 16 5 t one || eqN 16 5 t c

@[expose] noncomputable def bitsN (l : List Bool) : Nat :=
  l.foldr (fun b acc => 2 * acc + cond b 1 0) 0

@[expose] noncomputable def popN (x n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih x => Nat.add (Nat.land x 1) (ih (Nat.shiftRight x 1))) n x

@[expose] noncomputable def ueT (P M : Nat) (T : Nat → Nat) (lE : List Nat) : Bool :=
  Nat.beq M (hmask P lE) && lE.all fun e => eqN 16 5 (T (hN P e)) e

@[expose] noncomputable def ueI (lE LI YL YI : List Nat) : Bool :=
  LI == lE.map (invN 16 5) && YI == YL.map (invN 16 5)

@[expose] noncomputable def ueY (P M : Nat) (T : Nat → Nat) (c : Nat) (lS YL : List Nat) : Bool :=
  strictB c fun c => (lS.filter fun y => !memT P M T y && sqInN 16 5 c y) == YL

@[expose] noncomputable def ue2 (P M : Nat) (T : Nat → Nat) (GE lS : List Nat) : Bool :=
  lS.all fun s => strictB (invN 16 5 s) fun si =>
    GE.all fun g => memT P M T (pmN 16 5 (pmN 16 5 s g) si)

@[expose] noncomputable def ue5 (c : Nat) (lE LI : List Nat) : Bool :=
  strictB c fun c => strictB (pidn 16 5) fun one =>
    (lE.zip LI).all fun p => (lE.zip LI).all fun q => cInI one c p.1 p.2 q.1 q.2

@[expose] noncomputable def ueV (c : Nat) (lE LI YL YI MK : List Nat) : Bool :=
  strictB c fun c => strictB (pidn 16 5) fun one =>
    (MK == (YL.zip YI).map fun q => bitsN ((lE.zip LI).map fun p => cInI one c p.1 p.2 q.1 q.2)) &&
      MK.all fun m => Nat.ble (popN m lE.length) 32

@[expose] noncomputable def ue8 (P M : Nat) (T : Nat → Nat) (YL YI MK : List Nat) : Bool :=
  (YL.zip (YI.zip MK)).all fun p => (YL.zip MK).all fun q =>
    !Nat.beq p.2.2 q.2 || memT P M T (pmN 16 5 p.2.1 q.1)

@[expose] noncomputable def ueR (GE GS : List Nat) (c : Nat) (lE lS : List Nat) : Bool :=
  strictB c fun c =>
    GE.all (memN 16 5 lS) && memN 16 5 lE c && lE.all (sqInN 16 5 c) &&
      GS.any (fun a => GS.any fun b => !memN 16 5 lE (comN 16 5 a b))

end CFSG.KC.YoshQ

end
