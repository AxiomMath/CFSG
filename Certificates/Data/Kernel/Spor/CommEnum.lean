module

public import Certificates.Data.Kernel.Spor.CommBase

public section

namespace CFSG.KC.CommEnum

open CFSG.KC.Enum CFSG.KC.CommBase

abbrev Cand : Type := Nat × Nat × List Nat

abbrev RepRec : Type := Nat × List (List Nat) × List Cand

abbrev Ent : Type := Nat × Cand

@[expose] noncomputable def isRep (R : List RepRec) (r : Nat) : Bool := anyL (fun q => Nat.beq q.1 r) R

@[expose] noncomputable def look (E : List Ent) (r : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun e _ ih => nIf(Nat.beq e.1 r, e.2.1, ih)) E

@[expose] noncomputable def labOK (n w m : Nat) (L : Nat → Nat) (nL O : Nat) : Bool :=
  allN n (fun p => allN nL (fun z => Nat.beq (pg w m O (pg w m (L z) p)) (pg w m O p)))

@[expose] noncomputable def candOK (w m : Nat) (L : Nat → Nat) (nL : Nat) (R : List RepRec)
    (c : Cand) : Bool :=
  bAnd(isRep R c.2.1, bAnd(lettersOK nL c.2.2, Nat.beq (wapp w m L c.2.2 c.2.1) c.1))

@[expose] noncomputable def repOK (n w m : Nat) (L : Nat → Nat) (nL O : Nat) (R : List RepRec)
    (q : RepRec) : Bool :=
  bAnd(Nat.blt q.1 n, bAnd(Nat.beq (pg w m O q.1) q.1,
  bAnd(allL (lettersOK nL) q.2.1,
  bAnd(allL (fun s => Nat.beq (wapp w m L s q.1) q.1) q.2.1,
  bAnd(allL (candOK w m L nL R) q.2.2,
  allN n (fun y => bIf(fixAll w m L q.2.1 y, anyL (fun c => Nat.beq c.1 y) q.2.2, true)))))))

@[expose] noncomputable def refuted (E : List Ent) : Bool :=
  anyL (fun e => anyL (fun e' => bAnd(Nat.beq e.2.2.1 e'.2.2.1, notB (Nat.beq e.1 e'.1))) E) E

@[expose] noncomputable def sqOK (w m : Nat) (L : Nat → Nat) (E : List Ent) : Bool :=
  allL (fun e => Nat.beq (wapp w m L e.2.2.2 (look E e.2.2.1)) e.1) E

@[expose] noncomputable def matchY (w m : Nat) (Y : Nat → Nat) (nY : Nat) (E : List Ent) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun k ih => bIf(allL (fun e => Nat.beq (pg w m (Y k) e.1) e.2.1) E, true, ih)) nY

@[expose] noncomputable def leafOK (w m : Nat) (L : Nat → Nat) (Y : Nat → Nat) (nY : Nat)
    (E : List Ent) : Bool :=
  bIf(refuted E, true, bIf(sqOK w m L E, true, matchY w m Y nY E))

@[expose] noncomputable def enumK (w m : Nat) (L : Nat → Nat) (Y : Nat → Nat) (nY : Nat)
    (R : List RepRec) : List Ent → Bool :=
  List.rec (motive := fun _ => List Ent → Bool) (fun E => leafOK w m L Y nY E)
    (fun q _ ih E => allL (fun c => ih ((q.1, c) :: E)) q.2.2) R

@[expose] noncomputable def toB (R : List RepRec) : List BaseRec :=
  List.rec (motive := fun _ => List BaseRec) [] (fun q _ ih => (q.1, [], [], [], q.1) :: ih) R

@[expose] noncomputable def enumOK (n w m : Nat) (L : Nat → Nat) (nL : Nat) (R : List RepRec)
    (O PF ZF DF : Nat) (Y : Nat → Nat) (nY : Nat) : Bool :=
  bAnd(labOK n w m L nL O, bAnd(allL (repOK n w m L nL O R) R,
  bAnd(forestOK n w m L nL (toB R) PF ZF DF, enumK w m L Y nY R [])))

end CFSG.KC.CommEnum

end
