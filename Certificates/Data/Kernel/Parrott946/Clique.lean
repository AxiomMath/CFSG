module

public import Certificates.Data.Kernel.A45Cls.Over

public section

namespace CFSG.KC.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.BfsPin

@[expose] noncomputable def bitB (m k : Nat) : Bool :=
  Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) k))

@[expose] noncomputable def lane (W L k : Nat) : Nat :=
  Nat.land (Nat.shiftRight L (Nat.mul W k)) (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1))

@[expose] noncomputable def packL (W : Nat) (C : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun c _ ih => Nat.lor c (Nat.shiftLeft ih W)) C

@[expose] noncomputable def allL (L : List Nat) (f : Nat → Nat → Bool) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih k => bAnd(f k x, ih (Nat.succ k))) L

@[expose] noncomputable def anyL (L : List Nat) (f : Nat → Nat → Bool) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun x _ ih k => Bool.rec (motive := fun _ => Bool) (ih (Nat.succ k)) true (f k x)) L

@[expose] noncomputable def rowK (n w x : Nat) (J : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun y _ ih k => Nat.lor (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Nat.shiftLeft (nat_lit 1) k) (eq22 n w (mask w) x y y x)) (ih (Nat.succ k))) J

@[expose] noncomputable def cmK (n w : Nat) (I J : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun C => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) C)
    (fun x _ ih C => List.rec (motive := fun _ => Bool) false
      (fun c cs _ => bAnd(Nat.beq (rowK n w x J (nat_lit 0)) c, ih cs)) C) I

@[expose] noncomputable def triK (Ms : List Nat) (t : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun m _ ih => Nat.lor (Bool.rec (motive := fun _ => Nat) (nat_lit 0) m
      (Nat.beq (Nat.land m t) t)) ih) Ms

@[expose] noncomputable def aboveK (d c : Nat) : Nat :=
  Nat.shiftLeft (Nat.shiftRight d (Nat.succ c)) (Nat.succ c)

@[expose] noncomputable def bits3 (a b c : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.shiftLeft (nat_lit 1) a) (Nat.shiftLeft (nat_lit 1) b))
    (Nat.shiftLeft (nat_lit 1) c)

@[expose] noncomputable def cliqueK (W C : Nat) (Ms : List Nat) : Bool :=
  allN W fun a => strictB (lane W C a) fun ca =>
    allN W fun b => !bAnd(Nat.blt a b, bitB ca b) ||
      strictB (Nat.land ca (lane W C b)) fun cab =>
        allN W fun c => !bAnd(Nat.blt b c, bitB cab c) ||
          strictB (aboveK (Nat.land cab (lane W C c)) c) fun d =>
            Nat.beq (Nat.land d (triK Ms (bits3 a b c))) d

@[expose] noncomputable def inMaskK (I : List Nat) (m e P : Nat) : Bool :=
  Nat.beq P e || anyL I (fun k y => bAnd(bitB m k, Nat.beq y P)) (nat_lit 0)

@[expose] noncomputable def closedK (n w : Nat) (I : List Nat) (m e : Nat) : Bool :=
  allL I (fun a x => !bitB m a ||
    allL I (fun b y => !bitB m b || inMaskK I m e (pcomp n w (mask w) x y)) (nat_lit 0)) (nat_lit 0)

@[expose] noncomputable def appK (L R : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) R (fun x _ ih => x :: ih) L

@[expose] noncomputable def mapK (f : Nat → Nat) (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ ih => f x :: ih) L

@[expose] noncomputable def spanK (n w e : Nat) (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [e]
    (fun g _ ih => appK ih (mapK (pcomp n w (mask w) g) ih)) L

@[expose] noncomputable def hitK (I : List Nat) (P : Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun y _ ih k => Nat.lor (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Nat.shiftLeft (nat_lit 1) k) (Nat.beq y P)) (ih (Nat.succ k))) I

@[expose] noncomputable def hitE (W : Nat) (I : List Nat) (e P : Nat) : Nat :=
  strictN (Nat.lor (hitK I P (nat_lit 0))
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.shiftLeft (nat_lit 1) W) (Nat.beq P e)))
    fun h => nIf(Nat.beq h (nat_lit 0), Nat.shiftLeft (nat_lit 1) (Nat.succ W), h)

@[expose] noncomputable def coverK (W : Nat) (I : List Nat) (e : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun P _ ih => Nat.lor (hitE W I e P) ih) L

@[expose] noncomputable def idxBit (n w : Nat) (ps : List Nat) (N : Nat) (T S : Nat → Nat) (P : Nat) :
    Nat :=
  strictN (findK n w ps T S (pkeyK n w ps P) (nat_lit 24) (nat_lit 0) N) fun j =>
    nIf(bAnd(Nat.blt j N, Nat.beq (T j) P), Nat.shiftLeft (nat_lit 1) j, Nat.shiftLeft (nat_lit 1) N)

@[expose] noncomputable def idxCoverK (n w : Nat) (ps : List Nat) (N : Nat) (T S : Nat → Nat)
    (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun P _ ih => Nat.lor (idxBit n w ps N T S P) ih) L

@[expose] noncomputable def ltChainK (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih lo => bAnd(Nat.blt lo x, ih x)) L

@[expose] noncomputable def lenK (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def distinctK (L : List Nat) : Bool :=
  allL L (fun i x => allL L (fun j y => Nat.beq i j || !Nat.beq x y) (nat_lit 0)) (nat_lit 0)

@[expose] noncomputable def mulClosedK (n w : Nat) (L : List Nat) : Bool :=
  allL L (fun _ x => allL L (fun _ y => strictB (pcomp n w (mask w) x y) fun z =>
    anyL L (fun _ v => Nat.beq v z) (nat_lit 0)) (nat_lit 0)) (nat_lit 0)

@[expose] noncomputable def normMaskK (n w : Nat) (I : List Nat) (m e c : Nat) (gs : List Nat) :
    Bool :=
  allL gs (fun _ g => eq22 n w (mask w) c g e c ||
    anyL I (fun k y => bAnd(bitB m k, eq22 n w (mask w) c g y c)) (nat_lit 0)) (nat_lit 0)

end CFSG.KC.Parrott946

end
