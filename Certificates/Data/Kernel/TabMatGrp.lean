module

public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.F2Word

public section

namespace CFSG.KC.TabMatGrp

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W

@[expose] def natW {m : Nat} (w : List (Fin m × Bool)) : List (Nat × Bool) :=
  w.map fun l => (l.1.val, l.2)

@[expose] def pairLetter (z : Int) : Fin 2 × Bool :=
  if z = 1 then (0, true) else if z = -1 then (0, false) else if z = 2 then (1, true) else (1, false)

@[expose] noncomputable def letP (MA MAi MB MBi : Nat) (l : Nat × Bool) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun g b =>
    Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) MBi MB b)
      (Bool.rec (motive := fun _ => Nat) MAi MA b) (Nat.beq g (nat_lit 0))) l

@[expose] noncomputable def wordFrom (d MA MAi MB MBi : Nat) (w : List (Nat × Bool)) (acc : Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (mulW d acc (letP MA MAi MB MBi l)) ih) w acc

@[expose] noncomputable def wordP (d MA MAi MB MBi : Nat) (w : List (Nat × Bool)) : Nat :=
  wordFrom d MA MAi MB MBi w (idF d)

@[expose] noncomputable def invW (w : List (Nat × Bool)) : List (Nat × Bool) :=
  List.rec (motive := fun _ => List (Nat × Bool) → List (Nat × Bool)) (fun acc => acc)
    (fun l _ ih acc => ih (Prod.rec (motive := fun _ => Nat × Bool)
      (fun g b => (g, Bool.rec (motive := fun _ => Bool) true false b)) l :: acc)) w []

@[expose] noncomputable def segsK (d MA MAi MB MBi : Nat) (segs : List (List (Nat × Bool)))
    (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun s _ ih k => strictB (wordP d MA MAi MB MBi s) fun g =>
      strictB (wordP d MA MAi MB MBi (invW s)) fun gi => ih fun L => k (g :: gi :: L)) segs k

@[expose] noncomputable def gP (Gs : List Nat) (l : Nat × Bool) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun i b =>
    getL (nat_lit 0) Gs (Bool.rec (motive := fun _ => Nat) (Nat.succ (Nat.mul (nat_lit 2) i))
      (Nat.mul (nat_lit 2) i) b)) l

@[expose] noncomputable def segFrom (d : Nat) (Gs : List Nat) (w : List (Nat × Bool)) (acc : Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (mulW d acc (gP Gs l)) ih) w acc

@[expose] noncomputable def seedsK (d MA MB eA eB : Nat) (k : Nat → Nat → Bool) : Bool :=
  strictB (powK d MA (Nat.pred eA)) fun MAi => strictB (powK d MB (Nat.pred eB)) fun MBi =>
    andB (Nat.beq (mulF d MA MAi) (idF d)) (andB (Nat.beq (mulF d MB MBi) (idF d)) (k MAi MBi))

@[expose] noncomputable def pairsP (d MA MAi MB MBi : Nat) (Gs : List Nat)
    (ps : List (List (Nat × Bool) × List (Nat × Bool))) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => andB (Prod.rec (motive := fun _ => Bool) (fun w t =>
      Nat.beq (wordFrom d MA MAi MB MBi t (segFrom d Gs w (idF d))) (idF d)) p) ih) ps

@[expose] noncomputable def grpK (d MA MB eA eB : Nat) (segs : List (List (Nat × Bool)))
    (ps : List (List (Nat × Bool) × List (Nat × Bool))) : Bool :=
  seedsK d MA MB eA eB fun MAi MBi =>
    segsK d MA MAi MB MBi segs fun Gs => pairsP d MA MAi MB MBi Gs ps

@[expose] noncomputable def notInL (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih => andB (notB (Nat.beq x y)) ih) L

@[expose] noncomputable def distinctL (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x l ih => andB (notInL x l) ih) L

@[expose] noncomputable def matsK (d : Nat) (Gs : List Nat) (ws : List (List (Nat × Bool)))
    (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun acc => k acc)
    (fun w _ ih acc => strictB (segFrom d Gs w (idF d)) fun g => ih (g :: acc)) ws []

@[expose] noncomputable def distK (d MA MB eA eB : Nat) (segs : List (List (Nat × Bool)))
    (ws : List (List (Nat × Bool))) : Bool :=
  seedsK d MA MB eA eB fun MAi MBi =>
    segsK d MA MAi MB MBi segs fun Gs => matsK d Gs ws distinctL

end CFSG.KC.TabMatGrp

end
