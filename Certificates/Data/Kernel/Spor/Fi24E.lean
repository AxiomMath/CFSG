module

public import Certificates.Data.Kernel.Spor.Fi24Oct

public section

namespace CFSG.KC.Fi24E

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.Fi24Net
  CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Oct

@[expose] noncomputable def selW (ws : List (List Nat)) (v j : Nat) : List (List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => List.nil)
    (fun w _ ih i => Bool.rec (motive := fun _ => List (List Nat)) (ih (Nat.succ i))
      (w :: ih (Nat.succ i)) (Nat.beq (bitN v i) (nat_lit 1))) ws j

@[expose] noncomputable def vC (ws : List (List Nat)) (v : Nat) : List Nat :=
  prodC (selW ws v (nat_lit 0))

@[expose] noncomputable def same (F p : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.xor ptsM F) F (Nat.beq (bitN F p) (nat_lit 1))

@[expose] noncomputable def sigs (NW : Nat → Nat → Nat) (NT : Nat → Nat) (ws : List (List Nat))
    (p q : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (Nat.lor ptsM (Nat.shiftLeft ptsM (nat_lit 524288)))
    (fun w _ ih => strictN ih (fun a => strictN (fixC NW NT (dW w)) (fun F =>
      Nat.land a (Nat.lor (same F p) (Nat.shiftLeft (same F q) (nat_lit 524288)))))) ws

@[expose] noncomputable def cutP (NW : Nat → Nat → Nat) (NT : Nat → Nat) (ws : List (List Nat))
    (F q S : Nat) (tv : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) S
    (fun t _ ih => strictN ih (fun a => strictN (wkC NW NT (vC ws t) F) (fun C =>
      Nat.land a (same C q)))) tv

@[expose] noncomputable def pl1 (pp : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun e _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) e.1) ih) pp

@[expose] noncomputable def zipL (l m : List Nat) : List (Nat × Nat) :=
  List.rec (motive := fun _ => List Nat → List (Nat × Nat)) (fun _ => List.nil)
    (fun a _ ih m => List.rec (motive := fun _ => List (Nat × Nat)) List.nil
      (fun b t _ => (a, b) :: ih t) m) l m

@[expose] noncomputable def ppOK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (ws : List (List Nat))
    (p q : Nat) (pp : List (Nat × Nat)) : Bool :=
  allL (fun e => andB (Nat.beq (ptC NW NT (vC ws e.2) p) p)
    (Nat.beq (ptC NW NT (vC ws e.2) q) e.1)) pp

@[expose] noncomputable def passOK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (ws : List (List Nat))
    (p q : Nat) (c tv : List Nat) (pp : List (Nat × Nat)) (n P : Nat) : Bool :=
  andB (Nat.beq (popcount (Nat.land P (ones (nat_lit 524288))) (nat_lit 524288)) n)
    (andB (letB (fixC NW NT c) (fun F =>
        letB (cutP NW NT ws F q (Nat.shiftRight P (nat_lit 524288)) tv) (fun C =>
          Nat.beq (Nat.land C (pl1 pp)) C)))
      (ppOK NW NT ws p q pp))

@[expose] noncomputable def sigOK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (ws : List (List Nat))
    (p q : Nat) (c tv : List Nat) (pp : List (Nat × Nat)) (n : Nat) : Bool :=
  letB (sigs NW NT ws p q) (passOK NW NT ws p q c tv pp n)

@[expose] noncomputable def fixAll (NW : Nat → Nat → Nat) (NT : Nat → Nat) (css : List (List Nat)) :
    Nat :=
  List.rec (motive := fun _ => Nat) ptsM
    (fun cs _ ih => strictN ih (fun a => Nat.land (fixC NW NT cs) a)) css

@[expose] noncomputable def fixAllOK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (css : List (List Nat))
    (P : Nat) : Bool :=
  letB (fixAll NW NT css) (fun A => Nat.beq (Nat.land A P) A)

end CFSG.KC.Fi24E

end
