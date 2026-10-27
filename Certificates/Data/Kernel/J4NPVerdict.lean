module

public import Certificates.Data.Kernel.J4Q.QT
public import Certificates.Data.CFSGNative.J4Tree.M4Type

public section

namespace CFSG.KC.J4NPV

open CFSG.KC.Loop CFSG.KC.J4Q

structure Tabs where
  c : Nat
  rm : Nat
  one : Nat
  l5 : List Nat
  l5i : List Nat
  ge : List Nat
  gei : List Nat
  us : List Nat
  km : List Nat
  fm : List Nat

@[expose] noncomputable def prodFrom (c rm : Nat) (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun x _ ih acc => strictN (mulJ c rm acc x) ih) l

@[expose] noncomputable def prodK (c rm one : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) one (fun x xs _ => prodFrom c rm xs x) l

@[expose] noncomputable def selFrom (m : Nat) (Ts : List Nat) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun T _ ih j => Bool.rec (motive := fun _ => List Nat) (ih (Nat.succ j))
      (List.cons T (ih (Nat.succ j))) (bitB m j)) Ts

@[expose] noncomputable def maskK (T : Tabs) (Vs : List Nat) (m : Nat) : Nat :=
  prodK T.c T.rm T.one (selFrom m Vs (nat_lit 0))

@[expose] noncomputable def getsK (one : Nat) (Ms : List Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun i _ ih => List.cons (getN one Ms i) ih) l

@[expose] noncomputable def pcSeqK (e : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun s _ ih j => Bool.rec (motive := fun _ => List Nat) (ih (Nat.succ j))
      (List.append s (ih (Nat.succ j))) (bitB e j)) CFSG.J4Tree.Native.pcSeqsT (nat_lit 0)

@[expose] noncomputable def coordK (T : Tabs) (p : Nat × Nat) : Nat :=
  prodK T.c T.rm T.one (List.append (selFrom p.1 T.us (nat_lit 0)) (getsK T.one T.km (pcSeqK p.2)))

@[expose] noncomputable def coordsC (T : Tabs) (ps : List (Nat × Nat)) (k : List Nat → Bool) :
    Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k List.nil)
    (fun p _ ih k => strictB (coordK T p) fun v => ih fun vs => k (List.cons v vs)) ps k

@[expose] noncomputable def eltFrom (T : Tabs) (fs : List (String × List Int)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun f _ ih acc => ih (wordFrom T.c T.rm T.one T.ge T.gei f.2
      (wordFrom T.c T.rm T.one T.l5 T.l5i (w5K f.1.toList) acc))) fs

@[expose] noncomputable def eltK (T : Tabs) (fs : List (String × List Int)) : Nat :=
  eltFrom T fs T.one

@[expose] noncomputable def nilB (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l

@[expose] noncomputable def zipPre (f : Nat → Nat → Bool) (xs : List Nat) :
    List Nat → (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => List Nat → (List Nat → Bool) → Bool) (fun ms k => k ms)
    (fun x _ ih ms k => List.rec (motive := fun _ => Bool) false
      (fun m ms' _ => andB (f x m) (ih ms' k)) ms) xs

@[expose] noncomputable def coordOK (ps : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => andB (Nat.blt p.2 (nat_lit 1024)) ih) ps

@[expose] noncomputable def inE (ps : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => andB (Nat.beq p.2 (nat_lit 0)) ih) ps

@[expose] noncomputable def normEq (T : Tabs) (Vs : List Nat) (X x m : Nat) : Bool :=
  Nat.beq (mulJ T.c T.rm X x) (mulJ T.c T.rm (maskK T Vs m) X)

@[expose] noncomputable def normGo (T : Tabs) (Vs : List Nat) (skip : Bool) (S : List Nat)
    (k : List Nat → Bool) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) k
    (fun s _ ih ms => zipPre (fun v m => orB skip (normEq T Vs s v m)) Vs ms ih) S

@[expose] noncomputable def conjK (T : Tabs) (G : Nat) (Ws Vs : List Nat) : Bool :=
  zipPre (fun w v => Nat.beq (mulJ T.c T.rm w G) (mulJ T.c T.rm G v)) Ws Vs nilB

@[expose] noncomputable def npB (T : Tabs) (d : CFSG.J4Tree.VerdictJ.NPData) : Bool :=
  andB (coordOK (CFSG.J4Tree.Native.treeWv d.node)) (andB (coordOK d.V)
    (strictB (eltK T d.g) fun G =>
      coordsC T (CFSG.J4Tree.Native.treeWv d.node) fun Ws => coordsC T d.V fun Vs =>
        andB (conjK T G Ws Vs)
          (normGo T Vs (inE d.V) T.us (normGo T Vs false T.km nilB) d.masks)))

@[expose] noncomputable def fB (T : Tabs) (d : CFSG.J4Tree.VerdictJ.FData) : Bool :=
  andB (coordOK (CFSG.J4Tree.Native.treeWv d.node))
    (strictB (eltK T d.d) fun D =>
      coordsC T (CFSG.J4Tree.Native.treeWv d.node) fun Ws =>
        zipPre (fun f m => normEq T Ws D f m) T.fm d.masks nilB)

@[expose] noncomputable def conjB (T : Tabs) (src : List (Nat × Nat)) (d : CFSG.J4Tree.M4.ConjD) :
    Bool :=
  andB (coordOK src) (andB (coordOK d.tgt)
    (strictB (wordJ T.c T.rm T.one T.ge T.gei d.word) fun G =>
      coordsC T src fun S => coordsC T d.tgt fun Tt =>
        andB (zipPre (fun s m => normEq T Tt G s m) S d.fwd nilB)
          (zipPre (fun t m => Nat.beq (mulJ T.c T.rm t G) (mulJ T.c T.rm G (maskK T S m)))
            Tt d.bwd nilB)))

@[expose] noncomputable def invsK (c rm one pad : Nat) (gs hs : List Nat) : Bool :=
  zipPre (fun g h => andB (canonJ pad h) (Nat.beq (mulJ c rm g h) one)) gs hs nilB

@[expose] noncomputable def commK (c rm : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x xs ih => andB (List.rec (motive := fun _ => Bool) true
      (fun y _ ih' => andB (Nat.beq (mulJ c rm x y) (mulJ c rm y x)) ih') xs) ih) l

@[expose] noncomputable def wordsK (c rm one : Nat) (mats invs : List Nat) (Ms : List Nat)
    (ws : List (List Int)) : Bool :=
  List.rec (motive := fun _ => List (List Int) → Bool)
    (fun ws => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ws)
    (fun M _ ih ws => List.rec (motive := fun _ => Bool) false
      (fun w ws' _ => andB (Nat.beq M (wordJ c rm one mats invs w)) (ih ws')) ws) Ms ws

@[expose] noncomputable def dropK {α : Type} (n : Nat) (l : List α) : List α :=
  Nat.rec (motive := fun _ => List α → List α) (fun l => l)
    (fun _ ih l => ih (List.rec (motive := fun _ => List α) List.nil (fun _ t _ => t) l)) n l

@[expose] noncomputable def takeK {α : Type} (n : Nat) (l : List α) : List α :=
  List.rec (motive := fun _ => Nat → List α) (fun _ => List.nil)
    (fun x _ ih n => Nat.rec (motive := fun _ => List α) List.nil (fun j _ => List.cons x (ih j)) n)
    l n

@[expose] noncomputable def allK {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun d _ ih => andB (f d) ih) l

@[expose] noncomputable def chunkB {α : Type} (f : α → Bool) (n : Nat) (ds : List α) (i : Nat) :
    Bool :=
  allK f (takeK n (dropK (Nat.mul n i) ds))

end CFSG.KC.J4NPV

end
