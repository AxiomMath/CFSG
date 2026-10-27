module

public import Certificates.Data.Kernel.Spor.Fi24Kit
public import Certificates.Data.Kernel.Spor.Fi24FixP

public section

namespace CFSG.KC.Fi24ThreeO

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.Fi24Net
  CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit

@[expose] noncomputable def plC (NW : Nat → Nat → Nat) (NT : Nat → Nat) (c v : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 26), netF NT v, planeL NW c v)

@[expose] noncomputable def apC (NW : Nat → Nat → Nat) (NT : Nat → Nat) (c x : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 26), ptF NT x, letN NW c x)

@[expose] noncomputable def ptC (NW : Nat → Nat → Nat) (NT : Nat → Nat) (cs : List Nat) (x : Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat) x (fun c _ ih => strictN ih (apC NW NT c)) cs

@[expose] noncomputable def wkC (NW : Nat → Nat → Nat) (NT : Nat → Nat) (cs : List Nat) (v : Nat) :
    Nat :=
  Fi24FixP.walkP (plC NW NT) cs v

@[expose] noncomputable def invC (cs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun c _ ih => ih ++ [nIf(Nat.beq c (nat_lit 26), nat_lit 26, Nat.xor c (nat_lit 1))]) cs

@[expose] noncomputable def dW (W : List Nat) : List Nat := W ++ (nat_lit 26 :: invC W)

@[expose] noncomputable def fixC (NW : Nat → Nat → Nat) (NT : Nat → Nat) (cs : List Nat) : Nat :=
  Fi24FixP.fixS (wkC NW NT cs)

@[expose] noncomputable def cubeOK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (w : List Nat) : Bool :=
  Nat.beq (fixC NW NT (w ++ (w ++ w))) ptsM

@[expose] noncomputable def plOf (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) x) ih) l

@[expose] noncomputable def allL {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => andB (f a) ih) l

@[expose] noncomputable def allI {α : Type} (f : Nat → α → Bool) (l : List α) (i : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun a _ ih i => andB (f i a) (ih (Nat.succ i))) l i

@[expose] noncomputable def bitN (n i : Nat) : Nat := Nat.land (Nat.shiftRight n i) (nat_lit 1)

@[expose] noncomputable def incL (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun a _ ih p => andB (Nat.ble p a) (ih (Nat.succ a))) l (nat_lit 0)

@[expose] noncomputable def lenL {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def plG (gq : List (Nat × List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun g _ ih => strictN ih (fun a => Nat.lor (plOf g.2) a)) gq

@[expose] noncomputable def pl3 (ep : List (Nat × Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun e _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) e.1) ih) ep

@[expose] noncomputable def ncL (OL NT : Nat → Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a t ih => andB (allL (fun b => notB (Nat.beq (clsK OL NT a b) b)) t) ih) l

@[expose] noncomputable def ctP (NW : Nat → Nat → Nat) (NT : Nat → Nat) (FT : Nat) (W : List Nat) :
    Nat :=
  wkC NW NT (invC W) FT

@[expose] noncomputable def sepOK (NW : Nat → Nat → Nat) (NT OL : Nat → Nat) (w : List Nat)
    (tw : List (List Nat)) (gq : List (Nat × List Nat)) : Bool :=
  letB (fixC NW NT w) (fun FS => letB (fixC NW NT [nat_lit 26]) (fun FT =>
    letB (Nat.shiftLeft (nat_lit 1) (lenL tw)) (fun M =>
      andB (allI (fun j W => letB (ctP NW NT FT W) (fun C =>
          allL (fun g => letB (bitN g.1 j) (fun b =>
            allL (fun k => Nat.beq (bitN C k) b) g.2)) gq)) tw (nat_lit 0))
        (andB (incL (List.rec (motive := fun _ => List Nat) List.nil (fun g _ ih => g.1 :: ih) gq))
        (andB (allL (fun g => andB (Nat.blt g.1 M) (notB (Nat.beq g.1 (Nat.sub M (nat_lit 1))))) gq)
        (andB (allL (fun g => andB (incL g.2) (ncL OL NT g.2)) gq)
        (andB (Nat.beq (plG gq) FS)
          (allL (fun W => Nat.beq (bitN FS (ptC NW NT W (nat_lit 0))) (nat_lit 1)) tw))))))))

@[expose] noncomputable def pk19 (NW : Nat → Nat → Nat) (NT : Nat → Nat) (cs : List Nat) : Nat :=
  strictN (wkC NW NT cs (Fi24FixP.idPl19 (nat_lit 0))) (fun P0 =>
    Nat.rec (motive := fun _ => Nat) P0
      (fun k acc => strictN acc (fun a => Nat.lor a (Nat.shiftLeft
        (Nat.xor (wkC NW NT cs (Nat.xor (Fi24FixP.idPl19 (Nat.succ k)) (Fi24FixP.idPl19 (nat_lit 0)))) P0)
        (Nat.mul (Nat.succ k) (nat_lit 524288))))) (nat_lit 18))

@[expose] noncomputable def diffP (P Q : Nat) : Nat :=
  strictN (Nat.xor P Q) (fun D =>
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => strictN acc (fun a => Nat.lor a
        (Nat.land (Nat.shiftRight D (Nat.mul k (nat_lit 524288))) (ones (nat_lit 524288)))))
      (nat_lit 19))

@[expose] noncomputable def offS (NW : Nat → Nat → Nat) (NT : Nat → Nat) (cg cs : List Nat) : Nat :=
  strictN (pk19 NW NT cg) (fun G =>
    Nat.land (Nat.land ptsM (diffP G (pk19 NW NT [])))
      (Nat.land (diffP G (pk19 NW NT cs)) (diffP G (pk19 NW NT (cs ++ cs)))))

@[expose] noncomputable def gensOK (NW : Nat → Nat → Nat) (NT OL : Nat → Nat) (w : List Nat)
    (gp : List (List Nat × List Nat)) (en : List Nat) (ep : List (Nat × Nat × Nat)) : Bool :=
  letB (fixC NW NT w) (fun FS =>
    andB (allL (fun p => andB (Nat.beq (bitN FS (ptC NW NT p.1 0)) 1)
        (Nat.beq (bitN FS (ptC NW NT p.2 0)) 1)) gp)
    (andB (allL (fun k => notB (Nat.beq (clsK OL NT k (ptC NW NT w k)) (ptC NW NT w k))) en)
    (andB (allL (fun e => andB (andB (Nat.beq (bitN FS e.2.1) 1) (Nat.beq (bitN FS e.2.2) 1))
        (letB (clsK OL NT e.2.1 (clsK OL NT e.2.2 e.1)) (fun y =>
          andB (notB (Nat.beq y e.1)) (andB (notB (Nat.beq y (ptC NW NT w e.1)))
            (notB (Nat.beq y (ptC NW NT (w ++ w) e.1))))))) ep)
      (letB (List.rec (motive := fun _ => Nat) (Nat.lor FS (Nat.lor (plOf en) (pl3 ep)))
          (fun p _ ih => strictN ih (fun a => Nat.lor a (offS NW NT (dW p.1 ++ dW p.2) w))) gp)
        (fun A => Nat.beq (Nat.land A ptsM) ptsM)))))

@[expose] noncomputable def offOK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (cg cs : List Nat) (S : Nat) :
    Bool :=
  Nat.beq (Nat.land (Nat.land S ptsM) (offS NW NT cg cs)) (Nat.land S ptsM)

@[expose] noncomputable def stepW (NW : Nat → Nat → Nat) (NT : Nat → Nat) (ws : List (List Nat))
    (S : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) S (fun w _ ih => strictN ih (fun a => Nat.lor (wkC NW NT w S) a)) ws

@[expose] noncomputable def iterW (NW : Nat → Nat → Nat) (NT : Nat → Nat) (ws : List (List Nat))
    (d S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) S (fun _ ih => strictN ih (stepW NW NT ws)) d

@[expose] noncomputable def covW (NW : Nat → Nat → Nat) (NT : Nat → Nat) (ws : List (List Nat))
    (d S F : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.lor (iterW NW NT ws d S) F) ptsM) ptsM

@[expose] noncomputable def closW (NW : Nat → Nat → Nat) (NT : Nat → Nat) (ws : List (List Nat))
    (P : Nat) : Bool :=
  Nat.beq (stepW NW NT ws P) P

@[expose] noncomputable def orbOK (NW : Nat → Nat → Nat) (ls : List Nat) (d y c : Nat) : Bool :=
  letB (iterS NW ls d (Nat.shiftLeft (nat_lit 1) y)) (fun P =>
    andB (Nat.beq (stepS NW ls P) P) (Nat.beq (popcount P (nat_lit 524288)) c))

@[expose] noncomputable def itN (f : Nat → Nat) (n p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ ih => strictN ih f) n

@[expose] noncomputable def cycK (f : Nat → Nat) (p L : Nat) : Bool :=
  andB (Nat.beq (Nat.mod L (nat_lit 3)) (nat_lit 0)) (andB (notB (Nat.beq L (nat_lit 0)))
    (andB (Nat.beq (itN f L p) p) (notB (Nat.beq (itN f (Nat.div L (nat_lit 3)) p) p))))

@[expose] noncomputable def uP (NW : Nat → Nat → Nat) (OL NT : Nat → Nat) (k p : Nat) : Nat :=
  strictN (letN NW (nat_lit 2) k) (fun k1 => strictN (letN NW (nat_lit 2) k1) (fun k2 =>
    strictN (clsK OL NT k2 p) (fun y => strictN (clsK OL NT k1 y) (clsK OL NT k))))

end CFSG.KC.Fi24ThreeO

end
