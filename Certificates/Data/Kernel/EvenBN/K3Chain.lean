module

public import Certificates.Data.Kernel.EvenBN.YamadaK

public section

namespace CFSG.KC.K3Chain

open CFSG.KC.Enum CFSG.KC.F4Mat CFSG.KC.YamadaK

@[expose] noncomputable def baseK : Nat := 4415226413057

@[expose] def okL (i : Fin 10) : Bool :=
  Nat.beq i.val 0 || Nat.beq i.val 1 || Nat.beq i.val 4 || Nat.beq i.val 5 || Nat.beq i.val 6 ||
    Nat.beq i.val 8

@[expose] noncomputable def colEq (P B j : Nat) : Bool :=
  Nat.beq (ent P j) (ent B j) && Nat.beq (ent P (Nat.add 5 j)) (ent B (Nat.add 5 j)) &&
    Nat.beq (ent P (Nat.add 10 j)) (ent B (Nat.add 10 j)) &&
    Nat.beq (ent P (Nat.add 15 j)) (ent B (Nat.add 15 j)) &&
    Nat.beq (ent P (Nat.add 20 j)) (ent B (Nat.add 20 j))

@[expose] noncomputable def colKey (P j : Nat) : Nat :=
  Nat.add (ent P j) (Nat.mul 4 (Nat.add (ent P (Nat.add 5 j)) (Nat.mul 4 (Nat.add
    (ent P (Nat.add 10 j)) (Nat.mul 4 (Nat.add (ent P (Nat.add 15 j))
      (Nat.mul 4 (ent P (Nat.add 20 j)))))))))

@[expose] noncomputable def fixK (j P : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => ih && colEq P baseK k) j

@[expose] def incrFrom (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun a _ ih p => Nat.blt p a && ih a) l

@[expose] noncomputable def wordOK (j : Nat) (w : List (Fin 10)) : Bool :=
  w.all okL && strictB (mulK (wordK w) baseK) fun P => fixK j P

@[expose] noncomputable def imgKey (j : Nat) (w : List (Fin 10)) : Nat :=
  strictN (mulK (wordK w) baseK) fun P => colKey P j

@[expose] noncomputable def levelOK (j : Nat) (T : List (List (Fin 10))) : Bool :=
  T.all (wordOK j) && incrFrom (T.map (imgKey j)) 0

@[expose] noncomputable def levelsOK (Ts : List (List (List (Fin 10)))) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun T _ ih j => Nat.blt j 5 && levelOK j T && ih (Nat.succ j)) Ts

@[expose] noncomputable def chainK (Ts : List (List (List (Fin 10)))) : Bool := levelsOK Ts 0

end CFSG.KC.K3Chain
