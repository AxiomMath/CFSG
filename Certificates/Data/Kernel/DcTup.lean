module

public section

namespace CFSG.KC.DcTup

@[expose] noncomputable def forceN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def im (c p : Nat) : Nat :=
  Nat.land (Nat.shiftRight c (Nat.mul 14 p)) 16383

@[expose] noncomputable def imL (c : Nat) (ys : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun y _ ih => im c y :: ih) ys

@[expose] noncomputable def pk (ys : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun y _ ih => Nat.lor y (Nat.shiftLeft ih 14)) ys

@[expose] noncomputable def nth (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih j => Nat.rec (motive := fun _ => Nat) x (fun m _ => ih m) j) l i

@[expose] noncomputable def nthL (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih j => Nat.rec (motive := fun _ => List Nat) x (fun m _ => ih m) j) l i

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => Bool.rec (motive := fun _ => Bool) false ih (f i)) n

@[expose] noncomputable def allR (lo len : Nat) (f : Nat → Bool) : Bool :=
  allN len fun i => f (Nat.add lo i)

@[expose] noncomputable def invL (l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.sub l 2) (Nat.add l 2) (Nat.blt l 2)

@[expose] noncomputable def wordK (cs w : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) p (fun l _ ih => im (nth cs l) ih) w

@[expose] noncomputable def wordInvK (cs w : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun l _ ih q => ih (im (nth cs (invL l)) q)) w p

@[expose] noncomputable def wordInvL (cs w ps : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun p _ ih => wordInvK cs w p :: ih) ps

@[expose] noncomputable def tabOK (cs w : List Nat) (n X : Nat) : Bool :=
  allN n fun p => Nat.beq (im X p) (wordK cs w p)

@[expose] noncomputable def stepOK (n g Y X : Nat) : Bool :=
  allN n fun p => Nat.beq (im X p) (im g (im Y p))

@[expose] noncomputable def idOK (n X : Nat) : Bool :=
  allN n fun p => Nat.beq (im X p) p

@[expose] noncomputable def powOK (n : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e r _ => Bool.rec (motive := fun _ => Bool) false
      (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
        (fun x _ ih y => Bool.rec (motive := fun _ => Bool) false (ih x)
          (stepOK n (nth L 1) y x)) r e)
      (idOK n e)) L

@[expose] noncomputable def invOK (n c ci : Nat) : Bool :=
  allN n fun p => Nat.blt (im c p) n && Nat.blt (im ci p) n && Nat.beq (im ci (im c p)) p

@[expose] noncomputable def idx (N C Q2 za zb : Nat) : Nat :=
  forceN (Nat.land (Nat.shiftRight C (Nat.mul 26 za)) 67108863) fun c =>
    forceN (Nat.land c 8191) fun ka =>
      Bool.rec (motive := fun _ => Nat)
        (forceN (Nat.shiftRight c 13) fun kb =>
          Bool.rec (motive := fun _ => Nat) N kb (Nat.beq (im Q2 kb) zb))
        ka (Nat.beq (im Q2 ka) zb)

@[expose] noncomputable def row (RW k : Nat) : Nat :=
  Nat.land (Nat.shiftRight RW (Nat.mul 70 k)) 1180591620717411303423

@[expose] noncomputable def hitN (N C Q2 RW za zb : Nat) (zs : List Nat) : Nat :=
  forceN (idx N C Q2 za zb) fun k =>
    Bool.rec (motive := fun _ => Nat) 0
      (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq (pk zs) (row RW k)))
      (Nat.blt k N)

@[expose] noncomputable def walk (fin : Nat → Nat → List Nat → Nat → Nat)
    (Ls : List (List Nat)) : Nat → Nat → List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → List Nat → Nat → Nat) fin
    (fun L _ ih ya yb ys acc =>
      List.rec (motive := fun _ => Nat → Nat) (fun a => a)
        (fun u _ ih2 a =>
          forceN (forceN (im u ya) fun pa => forceN (im u yb) fun pb => ih pa pb (imL u ys) a) ih2)
        L acc)
    Ls

@[expose] noncomputable def walkP (fin : Nat → Nat → List Nat → Nat → Nat)
    (Ls : List (List Nat)) (ys : List Nat) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) acc
    (fun ya r _ => List.rec (motive := fun _ => Nat) acc
      (fun yb zs _ => walk fin Ls ya yb zs acc) r) ys

@[expose] noncomputable def cntF (X N C Q2 RW : Nat) (ya yb : Nat) (ys : List Nat) (acc : Nat) :
    Nat :=
  Nat.add acc (hitN N C Q2 RW (im X ya) (im X yb) (imL X ys))

@[expose] noncomputable def cntT (X N C Q2 RW : Nat) (Ls : List (List Nat)) (ys : List Nat) :
    Nat :=
  walkP (cntF X N C Q2 RW) Ls ys 0

@[expose] noncomputable def ordF (N C Q2 RW : Nat) (ya yb : Nat) (ys : List Nat) (acc : Nat) :
    Nat :=
  Bool.rec (motive := fun _ => Nat) 16384 (Nat.succ acc)
    (Nat.beq (idx N C Q2 ya yb) acc && Nat.beq (pk ys) (row RW acc))

@[expose] noncomputable def ordT (N C Q2 RW : Nat) (Ls : List (List Nat)) (ys : List Nat) : Nat :=
  walkP (ordF N C Q2 RW) Ls ys 0

@[expose] noncomputable def wtK (i j : Nat) : Nat :=
  forceN (Nat.add (Nat.add (Nat.mul i 1000003) j) 1) fun z =>
    Nat.mod (Nat.mul (Nat.mod (Nat.mul z z) 1000000007) z) 1000000007

@[expose] noncomputable def memN (c : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun x _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq x c)) l

@[expose] noncomputable def invK (n LB : Nat) (sel : List Nat) (X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun q ih s => forceN (Bool.rec (motive := fun _ => Nat) s
        (Nat.add s (wtK (im LB q) (im LB (im X q)))) (memN (im LB q) sel)) ih) n 0

@[expose] noncomputable def nthD {α : Type} (d : α) (l : List α) (i : Nat) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun x _ ih j => Nat.rec (motive := fun _ => α) x (fun m _ => ih m) j) l i

@[expose] noncomputable def lenK {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def allL {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih => Bool.rec (motive := fun _ => Bool) false ih (f x)) l

@[expose] noncomputable def edgeLK (rg rgi cs ws : List Nat) (Xs l q : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (wordInvK cs ws q) (im Xs q) (Nat.beq l 4))
      (im (nth rgi (Nat.sub l 2)) q) (Nat.blt l 4))
    (im (nth rg l) q) (Nat.blt l 2)

@[expose] noncomputable def evalEK (rg rgi cs ws : List Nat) (Xs : Nat) (e : List Nat)
    (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) p (fun l _ ih => edgeLK rg rgi cs ws Xs l ih) e

@[expose] noncomputable def edgeOK (m : Nat) (B rg rgi cs : List Nat) (X : Nat → Nat)
    (W : Nat → List Nat) (ed : Nat × Nat × List Nat) : Bool :=
  Nat.blt ed.1 m && Nat.blt ed.2.1 m && allL (fun l => Nat.blt l 6) ed.2.2 &&
    allL (fun b => Nat.beq (im (X ed.2.1) b) (evalEK rg rgi cs (W ed.1) (X ed.1) ed.2.2 b)) B

@[expose] noncomputable def inTreeK (m c0 : Nat) (E : List (Nat × Nat × List Nat))
    (inEdge dIn : List Nat) : Bool :=
  allN m fun i => Nat.beq i c0 ||
    (Nat.blt (nth inEdge i) (lenK E) &&
      Nat.beq (nthD (0, 0, []) E (nth inEdge i)).1 i &&
      Nat.blt (nth dIn (nthD (0, 0, []) E (nth inEdge i)).2.1) (nth dIn i))

@[expose] noncomputable def outTreeK (c0 : Nat) (reach : List Nat) (E : List (Nat × Nat × List Nat))
    (outEdge dOut : List Nat) : Bool :=
  allL (fun j => Nat.beq j c0 ||
    (Nat.blt (nth outEdge j) (lenK E) &&
      Nat.beq (nthD (0, 0, []) E (nth outEdge j)).2.1 j &&
      memN (nthD (0, 0, []) E (nth outEdge j)).1 reach &&
      Nat.blt (nth dOut (nthD (0, 0, []) E (nth outEdge j)).1) (nth dOut j))) reach

@[expose] noncomputable def allNeK (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x xs ih => allL (fun y => !Nat.beq y x) xs && ih) l

@[expose] noncomputable def memP (i j : Nat) (P : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun x _ ih => (Nat.beq x.1 i && Nat.beq x.2 j) || ih) P

@[expose] noncomputable def distK (m : Nat) (IV : List Nat) (P : List (Nat × Nat)) : Bool :=
  allN m fun j => allN j fun i => !Nat.beq (nth IV i) (nth IV j) || memP i j P

@[expose] noncomputable def massK (N : Nat) (H : Nat → Nat) (js : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun j _ ih => Nat.add (Nat.mul N (Nat.div N (H j))) ih) js

end CFSG.KC.DcTup

end
