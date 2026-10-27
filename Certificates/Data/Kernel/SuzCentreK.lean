module

public import Certificates.Data.Kernel.HexaK
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18SuzCenterData
public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.KC.SuzCentreK

open CFSG.KC.Enum CFSG.KS CFSG.KC.HexaK CFSG.ComponentClassification.AS81.SuzCenter
open CFSG.KLie.CT (anyN andB orB notB)

@[expose] noncomputable def allL (l : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) l

@[expose] noncomputable def anyL (l : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => orB (f x) ih) l

@[expose] noncomputable def cntL (l : List Nat) (f : Nat → Bool) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => strictN ih fun c => Bool.rec (motive := fun _ => Nat) c (Nat.succ c) (f x)) l

@[expose] noncomputable def lenL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def getL (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) l i

@[expose] noncomputable def nodupL (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih acc => andB (Nat.beq (Nat.land (Nat.shiftRight acc x) 1) 0)
      (ih (Nat.lor acc (Nat.shiftLeft 1 x)))) l (nat_lit 0)

@[expose] noncomputable def wordK (G : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn 1782 11)
    (fun j _ acc => strictN acc fun acc => mul 1782 11 (G j) acc) w

@[expose] noncomputable def wordsK (G : Nat → Nat) (ws : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun w _ ih => wordK G w :: ih) ws

@[expose] noncomputable def lettersK (g : Nat) (ws : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun w _ ih => andB (allL w fun j => Nat.blt j g) ih) ws

@[expose] noncomputable def fixAllK (t : Nat) (ps : List Nat) : Bool :=
  allL ps fun p => Nat.beq (pgC 1782 11 t p) p

@[expose] noncomputable def treeK (hs : List Nat) (L : CentreLevel) : Bool :=
  strictB (lenL L.pts) fun n =>
  andB (Nat.beq (lenL L.par) n) (andB (Nat.beq (lenL L.gen) n)
  (andB (Nat.blt 0 n) (andB (Nat.beq (getL L.pts 0) L.b)
  (andB (nodupL L.pts) (andB (allL L.pts fun x => Nat.blt x 1782)
    (allN n fun j => orB (Nat.beq j 0)
      (strictB (getL L.par j) fun p => strictB (getL L.gen j) fun k =>
        andB (Nat.blt p j) (andB (Nat.blt k (lenL hs))
          (Nat.beq (pgC 1782 11 (getL hs k) (getL L.pts p)) (getL L.pts j))))))))))

@[expose] noncomputable def levelsK (g : Nat) (G : Nat → Nat) (Ls : List CentreLevel) :
    List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun L _ ih B => andB (lettersK g L.ws)
      (andB (allL (wordsK G L.ws) fun t => fixAllK t B)
        (andB (treeK (wordsK G L.ws) L) (ih (L.b :: B))))) Ls

@[expose] noncomputable def prodK (Ls : List CentreLevel) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 1) (fun L _ ih => Nat.mul (lenL L.pts) ih) Ls

@[expose] noncomputable def basesK (O : List Nat) (Ls : List CentreLevel) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun L _ ih => andB (anyL O fun x => Nat.beq x L.b) ih) Ls

@[expose] noncomputable def centreBody (g : Nat) (G : Nat → Nat) (zw : List Nat)
    (Ls : List CentreLevel) (N : Nat) (L0 L1 : CentreLevel) : Bool :=
  strictB (wordK G zw) fun z =>
  andB (levelsK g G Ls []) (andB (Nat.beq (prodK Ls) N)
  (andB (allL L0.pts fun x => allN g fun k => anyL L0.pts fun y => Nat.beq y (pgC 1782 11 (G k) x))
  (andB (basesK L0.pts Ls)
  (andB (Nat.beq (cntL L0.pts fun x =>
      allL (wordsK G L1.ws) fun h => Nat.beq (pgC 1782 11 h x) x) 2)
  (andB (allL zw fun j => Nat.blt j g)
  (andB (allN g fun k => Nat.beq (mul 1782 11 z (G k)) (mul 1782 11 (G k) z))
    (notB (fixAllK z L0.pts))))))))

@[expose] noncomputable def centreK (g : Nat) (G : Nat → Nat) (zw : List Nat)
    (Ls : List CentreLevel) (N : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun L0 rest _ => List.rec (motive := fun _ => Bool) false
      (fun L1 _ _ => centreBody g G zw Ls N L0 L1) rest) Ls

end CFSG.KC.SuzCentreK

end
