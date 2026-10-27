module

public import Certificates.Data.ONanCMTab
public import CFSG.Certificates.Kernel.Spor.PK.Enc
public import CFSG.Mathlib.Decide.Nodup
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.OddStandard.ONanRec.CMK

open CFSG.OddStandard.ONanRec.CM CFSG.KC.Enum CFSG.KS CFSG.KS.PK

@[expose] noncomputable def packL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor x (Nat.shiftLeft ih (nat_lit 9))) l

@[expose] noncomputable def lenL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def allLt (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => Nat.blt x (nat_lit 480) && ih) l

@[expose] def genL (i : Nat) : List Nat := (cmGenTabs.toList.getD i #[]).toList

@[expose] noncomputable def genK (i : Nat) : Nat := packL (genL i)

@[expose] noncomputable def mulK (p q : Nat) : Nat := pcomp (nat_lit 480) (nat_lit 9) (mask (nat_lit 9)) p q

@[expose] noncomputable def idK : Nat := packL (List.range 480)

@[expose] noncomputable def lettersL : List Nat :=
  [genK 0, genK 0, genK 1, genK 1, genK 2, genK 2, genK 3, genK 3, genK 4, genK 4, genK 5,
    mulK (genK 5) (mulK (genK 5) (genK 5))]

@[expose] noncomputable def letK (c : Nat) : Nat := lettersL.getD c 0

@[expose] noncomputable def lettersK : Bool :=
  (List.range 6).all (fun i => lenL (genL i) == 480 && allLt (genL i)) &&
    (List.range 6).all fun i =>
      mulK (letK (2 * i + 1)) (letK (2 * i)) == idK && mulK (letK (2 * i)) (letK (2 * i + 1)) == idK

@[expose] noncomputable def wordK (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idK (fun c _ ih => strictN ih fun T => mulK (letK c) T) w

@[expose] noncomputable def ptK (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun c _ ih => fd 9 (letK c) ih) w

@[expose] noncomputable def relsK (ws : List (List Nat)) : Bool :=
  ws.all fun w => w.all (fun c => Nat.blt c 12) && wordK w == idK

@[expose] noncomputable def levelK (prev : List Nat) (L : ChainLevel) : Bool :=
  Nat.blt L.base 480 &&
    (L.words.all fun qw => qw.2.all (fun c => Nat.blt c 12) &&
      prev.all (fun b => ptK qw.2 b == b) && ptK qw.2 L.base == qw.1) &&
    CFSG.Decide.bitsetNodup (L.words.map Prod.fst)

@[expose] noncomputable def chainK : List Nat → List ChainLevel → Bool
  | _, [] => true
  | prev, L :: rest => levelK prev L && chainK (prev ++ [L.base]) rest

end CFSG.OddStandard.ONanRec.CMK
