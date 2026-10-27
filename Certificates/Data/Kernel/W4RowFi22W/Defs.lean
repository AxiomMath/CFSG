module

public import Certificates.Data.Kernel.Census.PackedBase

public section

namespace CFSG.KC.W4F22

open CFSG.KC.Enum CFSG.KC.Census

variable (w h : Nat) (L : Nat → Nat) (E : List (List Nat))

@[expose] noncomputable def actW (x : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun k _ ih p => strictN (at' w (L k) p) ih) x p

@[expose] noncomputable def actWI (x : List Nat) (p : Nat) : Nat :=
  actW w L (List.map (lsw h) (List.reverse x)) p

@[expose] noncomputable def refAct (r p : Nat) : Nat :=
  bif Nat.beq (Nat.mod r 2) 1 then actWI w h L (List.getD E (Nat.div r 2) []) p
  else actW w L (List.getD E (Nat.div r 2) []) p

@[expose] noncomputable def refsAct (rs : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun r _ ih p => strictN (refAct w h L E r p) ih) rs p

@[expose] noncomputable def relB (bs : List Nat) (rl : List Nat × List Nat) : Bool :=
  List.all bs fun b => Nat.beq (refsAct w h L E rl.1 b) (refsAct w h L E rl.2 b)

@[expose] noncomputable def movB (m : List Nat × Nat) : Bool :=
  Bool.not (Nat.beq (refsAct w h L E m.1 m.2) m.2)

@[expose] noncomputable def lettersB (m : Nat) : Bool :=
  List.all E fun x => List.all x fun k => Nat.blt k m

end CFSG.KC.W4F22

end
