module

public import Certificates.Data.Kernel.YoshQ.TabN

public section

namespace CFSG.KD.J2Five

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ

@[expose] noncomputable def pm (x y : Nat) : Nat := pmN (nat_lit 315) (nat_lit 9) x y

@[expose] noncomputable def eq (x y : Nat) : Bool := eqN (nat_lit 315) (nat_lit 9) x y

@[expose] noncomputable def one : Nat := pidn (nat_lit 315) (nat_lit 9)

@[expose] noncomputable def ap (x q : Nat) : Nat := pg (nat_lit 9) (mask (nat_lit 9)) x q

@[expose] noncomputable def getN (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih i => Nat.rec (motive := fun _ => Nat) a (fun j _ => ih j) i) L

@[expose] noncomputable def getW (L : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun a _ ih i => Nat.rec (motive := fun _ => List Nat) a (fun j _ => ih j) i) L

@[expose] noncomputable def lenN (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def lenW (L : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def lenR (R : List (Nat × List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) R

@[expose] noncomputable def letOK (m : Nat) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(Nat.blt a m, ih)) w

@[expose] noncomputable def wordN (G : List Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) one (fun a _ ih => pm (getN G a) ih) w

@[expose] noncomputable def wImg (G : List Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun a _ ih p => ap (getN G a) (ih p)) w

@[expose] noncomputable def wInv (Gi : List Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun a _ ih q => ih (ap (getN Gi a) q)) w

@[expose] noncomputable def keyN (G Gi : List Nat) (x p : Nat) (w : List Nat) : Nat :=
  wInv Gi w (ap x (wImg G w p))

@[expose] noncomputable def keysN (G Gi : List Nat) (x : Nat) (pts : List Nat) (w : List Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Nat.lor (keyN G Gi x p w) (Nat.shiftLeft ih (nat_lit 9))) pts

@[expose] noncomputable def conjGo (G Gi : List Nat) (x : Nat) (pts : List Nat) (m : Nat) :
    List (Nat × List Nat) → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih lo => Prod.rec (motive := fun _ => Bool)
      (fun k w => bAnd(Nat.ble lo k, bAnd(letOK m w,
        bAnd(Nat.beq (keysN G Gi x pts w) k, ih (Nat.succ k))))) r)

@[expose] noncomputable def conjOK (G Gi : List Nat) (x : Nat) (pts : List Nat)
    (R : List (Nat × List Nat)) : Bool :=
  conjGo G Gi x pts (lenN G) R (nat_lit 0)

@[expose] noncomputable def keyX (x : Nat) (pts : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Nat.lor (ap x p) (Nat.shiftLeft ih (nat_lit 9))) pts

@[expose] noncomputable def keyGo (S : List Nat) (pts : List Nat) (m : Nat) :
    List (List Nat) → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih lo => bAnd(letOK m w,
      strictB (keyX (wordN S w) pts) fun k => bAnd(Nat.ble lo k, ih (Nat.succ k))))

@[expose] noncomputable def elt (S : List Nat) (W : List (List Nat)) (i : Nat) : Nat :=
  wordN S (getW W i)

@[expose] noncomputable def grpOK (S pts : List Nat) (W C : List (List Nat)) (i₀ : Nat) : Bool :=
  bAnd(keyGo S pts (lenN S) W (nat_lit 0),
    bAnd(Nat.blt i₀ (lenW W), bAnd(eq (elt S W i₀) one,
      allN (lenW W) fun i => strictB (elt S W i) fun x =>
        allN (lenN S) fun j => strictB (getN (getW C i) j) fun q =>
          bAnd(Nat.blt q (lenW W), eq (pm x (getN S j)) (elt S W q)))))

@[expose] noncomputable def kleinOK (x u : Nat) : Bool :=
  strictB (pm x x) fun x2 => strictB (pm (pm x u) x2) fun u2 =>
    bAnd(eq (pm x x2) one, bAnd(eq (pm u u) one, bAnd(bIf(eq u one, false, true),
      bAnd(eq (pm u u2) (pm u2 u), bAnd(eq (pm (pm x u2) x2) (pm u u2),
        bIf(eq u2 u, false, true))))))

@[expose] noncomputable def getR (L : List (Nat × List Nat)) : Nat → Nat × List Nat :=
  List.rec (motive := fun _ => Nat → Nat × List Nat) (fun _ => (nat_lit 0, []))
    (fun a _ ih i => Nat.rec (motive := fun _ => Nat × List Nat) a (fun j _ => ih j) i) L

@[expose] noncomputable def gensOK (G : List Nat) : Bool :=
  bAnd(eq (pm (getN G 0) (getN G 0)) one,
    bAnd(eq (pm (getN G 1) (pm (getN G 1) (getN G 1))) one, eq (pm (getN G 2) (getN G 2)) one))

@[expose] noncomputable def ck3 (G : List Nat) (sw : List (List Nat)) (pts : List Nat)
    (W C K : List (List Nat)) (i₀ : Nat) : Bool :=
  bAnd(letOK (nat_lit 2) (getW sw 0), bAnd(letOK (nat_lit 2) (getW sw 1),
    strictB (wordN G (getW sw 0)) fun s0 => strictB (wordN G (getW sw 1)) fun s1 =>
      bAnd(grpOK [s0, s1] pts W C i₀, allN (lenW W) fun i =>
        bIf(Nat.beq i i₀, true, bAnd(letOK (nat_lit 2) (getW K i),
          kleinOK (elt [s0, s1] W i) (wordN G (getW K i)))))))

@[expose] noncomputable def conjTo (G : List Nat) (x a c : Nat) (r : Nat × List Nat) : Bool :=
  bAnd(letOK (nat_lit 3) r.2, strictB (wordN G r.2) fun h =>
    eq (pm x h) (pm h (nIf(Nat.beq r.1 (nat_lit 0), a, c))))

@[expose] noncomputable def zval (G : List Nat) (sw W : List (List Nat)) (i : Nat) : Nat :=
  elt [wordN G (getW sw 0), wordN G (getW sw 1)] W i

@[expose] noncomputable def ck5 (G : List Nat) (sw : List (List Nat)) (pts : List Nat)
    (W C : List (List Nat)) (i₀ zA zC : Nat) (H : List (Nat × List Nat)) (t3 : List Nat) : Bool :=
  bAnd(letOK (nat_lit 2) (getW sw 0), bAnd(letOK (nat_lit 2) (getW sw 1),
    strictB (wordN G (getW sw 0)) fun s0 => strictB (wordN G (getW sw 1)) fun s1 =>
      bAnd(grpOK [s0, s1] pts W C i₀, bAnd(eq (pm s0 s1) (pm s1 s0),
        strictB (elt [s0, s1] W zA) fun a => strictB (elt [s0, s1] W zC) fun c =>
          bAnd(allN (lenW W) (fun i => bIf(Nat.beq i i₀, true,
              conjTo G (elt [s0, s1] W i) a c (getR H i))),
            bAnd(letOK (nat_lit 3) t3, strictB (wordN G t3) (fun t =>
                bAnd(eq (pm t (pm t t)) one, bAnd(bIf(eq t one, false, true),
                  eq (pm t a) (pm a t))))))))))

@[expose] noncomputable def orbOK (G Gi : List Nat) (x : Nat) (pts : List Nat)
    (R : List (Nat × List Nat)) (c : Nat) : Bool :=
  bAnd(Nat.beq (lenR R) c, strictB x fun a => conjOK G Gi a pts R)

end CFSG.KD.J2Five

end
