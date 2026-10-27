module

public import Certificates.Data.Kernel.Co1F2

public section

namespace CFSG.KC.TabMat

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2

@[expose] noncomputable def letM (NA NAi NB NBi : Nat) (l : Nat × Bool) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun g b =>
    Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) NBi NB b)
      (Bool.rec (motive := fun _ => Nat) NAi NA b) (Nat.beq g (nat_lit 0))) l

@[expose] noncomputable def matW (d NA NAi NB NBi : Nat) (w : List (Nat × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) (idF d) (fun l _ ih => mulF d ih (letM NA NAi NB NBi l)) w

@[expose] noncomputable def invNAcc (w acc : List (Nat × Bool)) : List (Nat × Bool) :=
  List.rec (motive := fun _ => List (Nat × Bool) → List (Nat × Bool)) (fun acc => acc)
    (fun l _ ih acc => ih (Prod.rec (motive := fun _ => Nat × Bool)
      (fun g b => (g, Bool.rec (motive := fun _ => Bool) true false b)) l :: acc)) w acc

@[expose] noncomputable def invN (w : List (Nat × Bool)) : List (Nat × Bool) := invNAcc w []

@[expose] noncomputable def gensK (d NA NAi NB NBi : Nat) (segs : List (List (Nat × Bool)))
    (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun s _ ih k => strictB (matW d NA NAi NB NBi s) fun g =>
      strictB (matW d NA NAi NB NBi (invN s)) fun gi => ih fun L => k (g :: gi :: L)) segs k

@[expose] noncomputable def gM (GL : List Nat) (l : Nat × Bool) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun i b =>
    getL (nat_lit 0) GL (Bool.rec (motive := fun _ => Nat) (Nat.succ (Nat.mul (nat_lit 2) i))
      (Nat.mul (nat_lit 2) i) b)) l

@[expose] noncomputable def matG (d : Nat) (GL : List Nat) (w : List (Nat × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) (idF d) (fun l _ ih => mulF d ih (gM GL l)) w

@[expose] noncomputable def pairsK (d NA NAi NB NBi : Nat) (GL : List Nat)
    (ps : List (List (Nat × Bool) × List (Nat × Bool))) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => andB (Prod.rec (motive := fun _ => Bool) (fun w t =>
      Nat.beq (mulF d (matW d NA NAi NB NBi t) (matG d GL w)) (idF d)) p) ih) ps

@[expose] noncomputable def tabMatK (d NA NAi NB NBi : Nat) (segs : List (List (Nat × Bool)))
    (ps : List (List (Nat × Bool) × List (Nat × Bool))) : Bool :=
  gensK d NA NAi NB NBi segs fun GL => pairsK d NA NAi NB NBi GL ps

end CFSG.KC.TabMat

end
