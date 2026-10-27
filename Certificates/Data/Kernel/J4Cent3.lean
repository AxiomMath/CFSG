module

public import Certificates.Data.Kernel.J4Five
public import Certificates.Data.Kernel.SporSch.J4SCols

public section

namespace CFSG.KC.J4Cent3

open CFSG.KC.J4Count CFSG.KC.J4Q CFSG.KC.J4Five

@[expose] noncomputable def orb3 (z : List Nat) (t : Nat) : List Nat :=
  [t, getN 0 z t, getN 0 z (getN 0 z t)]

@[expose] noncomputable def octM (z Fl Tl : List Nat) (k : Nat) : Nat :=
  Nat.lor (maskL (Fl.eraseIdx k)) (maskL (orb3 z (getN 0 Tl k)))

@[expose] noncomputable def oct6OK (B P z Fl Tl : List Nat) : Bool :=
  allN (nat_lit 6) fun k => strictB (octM z Fl Tl k) fun O => strictB (maskL (Fl.eraseIdx k)) fun Fm =>
    andB (andB (Nat.beq (pcN O (nat_lit 24)) (nat_lit 8)) (inC B P O))
      (all64 (nat_lit 64) fun s => strictB (combo B s) fun a =>
        orB (notB (andB (Nat.beq (pcN a (nat_lit 24)) (nat_lit 8)) (Nat.beq (Nat.land a Fm) Fm)))
          (Nat.beq a O))

@[expose] noncomputable def crd16OK (z crd L : List Nat) : Bool :=
  allN (nat_lit 24) fun x => andB (Nat.blt (Nat.mod (getN 0 crd x) (nat_lit 16)) (nat_lit 12))
    (Nat.beq (zPow z (Nat.div (getN 0 crd x) (nat_lit 16))
      (getN 0 L (Nat.mod (getN 0 crd x) (nat_lit 16)))) x)

@[expose] noncomputable def bld16 (z crd c : List Nat) (x : Nat) : Nat :=
  zPow z (Nat.div (getN 0 crd x) (nat_lit 16)) (getN 0 c (Nat.mod (getN 0 crd x) (nat_lit 16)))

@[expose] def prodL : List (List Nat) → List (List Nat)
  | [] => [[]]
  | a :: as => a.flatMap fun x => (prodL as).map (x :: ·)

@[expose] noncomputable def allow3 (z Fl Tl : List Nat) : List (List Nat) :=
  [[getN 0 Fl 0], [getN 0 Fl 1], [getN 0 Fl 2], [getN 0 Fl 3], [getN 0 Fl 4, getN 0 Fl 5],
    [getN 0 Fl 4, getN 0 Fl 5], [getN 0 Tl 0], orb3 z (getN 0 Tl 1), orb3 z (getN 0 Tl 2),
    orb3 z (getN 0 Tl 3), orb3 z (getN 0 Tl 4) ++ orb3 z (getN 0 Tl 5),
    orb3 z (getN 0 Tl 4) ++ orb3 z (getN 0 Tl 5)]

@[expose] noncomputable def cands3 (z Fl Tl : List Nat) : List (List Nat) := prodL (allow3 z Fl Tl)

@[expose] noncomputable def cand3N (B P z crd Fl Tl : List Nat) : Nat :=
  ((cands3 z Fl Tl).filter fun c => genOK B P (bld16 z crd c)).length

@[expose] noncomputable def memK (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => orB (Nat.beq x y) ih) L

@[expose] noncomputable def starTabOK (PC : Nat) (S : List (List Nat)) (Z : List Nat) : Bool :=
  allN (nat_lit 24) fun i => List.rec (motive := fun _ => Bool) true
    (fun c _ ih => andB (memK (CFSG.KS.SporSch.C11.appK PC c) (S.getD (getN 0 Z i) [])) ih)
    (S.getD i [])

@[expose] def ZE : List Nat :=
  [0, 1, 11, 2, 19, 5, 21, 13, 7, 4, 23, 3, 20, 8, 10, 15, 6, 17, 12, 9, 18, 16, 22, 14]

@[expose] def FL3 : List Nat := [0, 1, 5, 15, 17, 22]

@[expose] def TL3 : List Nat := [4, 6, 7, 2, 12, 10]

@[expose] def CRD3 : List Nat :=
  [0, 1, 9, 41, 6, 2, 7, 8, 40, 38, 11, 25, 10, 24, 43, 3, 39, 4, 42, 22, 26, 23, 5, 27]

end CFSG.KC.J4Cent3

end
