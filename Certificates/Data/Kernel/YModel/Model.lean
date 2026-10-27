module

public import CFSG.Certificates.Kernel.MonsterConv.Perm
public import Certificates.Data.Kernel.YModel.Text

public section

namespace CFSG.KC.YModel

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop

@[expose] noncomputable def wid (k : Nat) : Nat := Nat.shiftLeft (nat_lit 1) k

@[expose] noncomputable def bitB (x b : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight x b) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def stageBit (k i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.sub (Nat.add i (nat_lit 1)) k)
    (Nat.sub (Nat.sub k (nat_lit 1)) i) (Nat.blt i k)

@[expose] noncomputable def netOK (k N : Nat) : Bool :=
  andB (Nat.blt N (Nat.shiftLeft (nat_lit 1) (Nat.mul (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 1)) (wid k))))
    (Nat.rec (motive := fun _ => Bool) true
      (fun i ih => andB (Nat.beq (Nat.land (Nat.land (Nat.shiftRight N (Nat.mul i (wid k))) (ones (wid k)))
        (idPlane (wid k) (stageBit k i))) (nat_lit 0)) ih)
      (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 1)))

@[expose] noncomputable def letOK (k n F N : Nat) : Bool :=
  andB (Nat.ble n (wid k)) (andB (netOK k N) (andB (highOK F (nat_lit 32) n k (nat_lit 1))
    (colOK F (nat_lit 32) n k (nat_lit 0) N)))

@[expose] noncomputable def apK (k N X : Nat) : Nat :=
  netApply k (wid k) (repU (wid k) k) N X

@[expose] noncomputable def wordAp (k m : Nat) (Nf : Nat → Nat) (w : List Nat) (X : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun c _ ih x => strictN (nIf(Nat.blt c m, apK k (Nf c) x, x)) ih) w X

@[expose] noncomputable def relsOK (k m : Nat) (Nf : Nat → Nat) (rels : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => andB (Nat.beq (wordAp k m Nf r (idP k)) (idP k)) ih) rels

@[expose] noncomputable def weqK (k m : Nat) (Nf : Nat → Nat) (u v : List Nat) : Bool :=
  Nat.beq (wordAp k m Nf u (idP k)) (wordAp k m Nf v (idP k))

@[expose] noncomputable def netRev (k N : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight N (Nat.mul i (wid k))) (ones (wid k)))
      (Nat.mul (Nat.sub (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 2)) i) (wid k))))
    (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 1))

@[expose] noncomputable def codeNet (k : Nat) (T : Nat → Nat) (x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (T (Nat.sub (Nat.shiftRight x (nat_lit 1)) (nat_lit 1)))
    (netRev k (T (Nat.sub (Nat.shiftRight x (nat_lit 1)) (nat_lit 1)))) (bitB x (nat_lit 0))

@[expose] noncomputable def wordNets (k w : Nat) (T : Nat → Nat) (P len : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih Q => List.cons (codeNet k T (Nat.land Q (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))))
      (ih (Nat.shiftRight Q w))) len P

@[expose] noncomputable def codesOK (w j P len : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih Q => (fun x => andB (Nat.blt (nat_lit 1) x) (andB (Nat.ble (Nat.shiftRight x (nat_lit 1)) j)
        (ih (Nat.shiftRight Q w))))
      (Nat.land Q (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)))) len P

@[expose] noncomputable def popc (k X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) X
    (fun b acc => strictN acc (fun a =>
      (fun s msk => Nat.add (Nat.land a msk) (Nat.land (Nat.shiftRight a s) msk))
        (Nat.shiftLeft (nat_lit 1) b) (Nat.xor (ones (wid k)) (idPlane (wid k) b)))) k

@[expose] noncomputable def fixesK (k : Nat) (T : Nat → Nat) (B j i : Nat) : Bool :=
  (fun fs => Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB (bitB fs (fieldAt (nat_lit 32) B t)) ih) i)
    (fixedSet k (apK k (T j) (idP k)))

@[expose] noncomputable def levelNets (k : Nat) (T : Nat → Nat) (B s i : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil
    (fun j ih => Bool.rec (motive := fun _ => List Nat) ih (List.cons (T j) ih) (fixesK k T B j i)) s

@[expose] noncomputable def wordOK (k w m : Nat) (T WP WL : Nat → Nat) (i : Nat) : Bool :=
  andB (netOK k (T (Nat.add m i))) (andB (codesOK w (Nat.add m i) (WP i) (WL i))
    (wordNet k (wordNets k w T (WP i) (WL i)) (T (Nat.add m i))))

@[expose] noncomputable def levelOK (k n s : Nat) (T : Nat → Nat) (B : Nat) (R M Z : Nat → Nat)
    (i : Nat) : Bool :=
  andB (Nat.blt (fieldAt (nat_lit 32) B i) n)
    (andB (orbitOK k (levelNets k T B s i) (fieldAt (nat_lit 32) B i) (R i) (M i))
      (Nat.beq (popc k (M i)) (Z i)))

@[expose] noncomputable def codesIn (w lo hi P len : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih Q => (fun x => andB (Nat.blt lo (Nat.shiftRight x (nat_lit 1)))
        (andB (Nat.ble (Nat.shiftRight x (nat_lit 1)) hi) (ih (Nat.shiftRight Q w))))
      (Nat.land Q (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)))) len P

@[expose] noncomputable def invW (w P len : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih Q acc => ih (Nat.shiftRight Q w)
      (Nat.lor (Nat.shiftLeft acc w)
        (Nat.xor (Nat.land Q (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))) (nat_lit 1))))
    len P (nat_lit 0)

@[expose] noncomputable def catW (w P1 L1 P2 : Nat) : Nat :=
  Nat.lor P1 (Nat.shiftLeft P2 (Nat.mul w L1))

@[expose] noncomputable def sweqK (k w : Nat) (U : Nat → Nat) (P1 L1 P2 L2 : Nat) : Bool :=
  Nat.beq (netsApply k (wid k) (repU (wid k) k) (wordNets k w U P1 L1) (idP k))
    (netsApply k (wid k) (repU (wid k) k) (wordNets k w U P2 L2) (idP k))

@[expose] noncomputable def mapsTo (k w : Nat) (U : Nat → Nat) (P len b x : Nat) : Bool :=
  Nat.beq (netsApply k (wid k) (nat_lit 1) (wordNets k w U P len) (Nat.shiftLeft (nat_lit 1) x))
    (Nat.shiftLeft (nat_lit 1) b)

@[expose] noncomputable def ptX (t : Nat) : Nat := Nat.land t (nat_lit 65535)
@[expose] noncomputable def ptL (t : Nat) : Nat := Nat.land (Nat.shiftRight t (nat_lit 16)) (nat_lit 65535)
@[expose] noncomputable def ptP (t : Nat) : Nat := Nat.shiftRight t (nat_lit 32)

@[expose] noncomputable def genOK (k w : Nat) (U WP WL : Nat → Nat) (lo hi j b : Nat) (fix : Bool) :
    Bool :=
  andB (netOK k (U j)) (andB (codesIn w lo hi (WP j) (WL j))
    (andB (wordNet k (wordNets k w U (WP j) (WL j)) (U j))
      (bIf(fix, Nat.beq (netApply k (wid k) (nat_lit 1) (U j) (Nat.shiftLeft (nat_lit 1) b))
        (Nat.shiftLeft (nat_lit 1) b), true))))

@[expose] noncomputable def transOK (k w : Nat) (U TT : Nat → Nat) (b lo hi a0 cnt : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun r ih => andB ((fun t => andB (codesIn w lo hi (ptP t) (ptL t))
        (mapsTo k w U (ptP t) (ptL t) b (ptX t))) (TT (Nat.add a0 r))) ih) cnt

@[expose] noncomputable def pointsOK (k : Nat) (TT : Nat → Nat) (Z : Nat) : Bool :=
  Nat.beq (popc k (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a acc => strictN acc (fun s => Nat.lor s (Nat.shiftLeft (nat_lit 1) (ptX (TT a))))) Z)) Z

@[expose] noncomputable def recOK (k w : Nat) (U TT : Nat → Nat) (Z hi top a j rec : Nat) : Bool :=
  (fun ty ta => andB (Nat.blt (ptX rec) Z)
    (bIf(Nat.beq (ptL rec) (nat_lit 65535),
      andB (Nat.beq (ptP ty) (catW w (Nat.mul (nat_lit 2) (Nat.succ j)) (nat_lit 1) (ptP ta)))
        (Nat.beq (ptL ty) (Nat.succ (ptL ta))),
      andB (codesIn w hi top (ptP rec) (ptL rec))
        (sweqK k w U
          (catW w (catW w (invW w (ptP ty) (ptL ty)) (ptL ty) (Nat.mul (nat_lit 2) (Nat.succ j)))
            (Nat.succ (ptL ty)) (ptP ta))
          (Nat.add (Nat.succ (ptL ty)) (ptL ta)) (ptP rec) (ptL rec)))))
    (TT (ptX rec)) (TT a)

@[expose] noncomputable def schOK (k w : Nat) (U TT : Nat → Nat) (Z lo hi top a0 cnt : Nat)
    (recs : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun r => Nat.beq r (Nat.mul cnt (Nat.sub hi lo)))
    (fun rec _ ih r => andB (Nat.blt r (Nat.mul cnt (Nat.sub hi lo)))
      (andB (recOK k w U TT Z hi top (Nat.add a0 (Nat.div r (Nat.sub hi lo)))
          (Nat.add lo (Nat.mod r (Nat.sub hi lo))) rec)
        (strictB (Nat.succ r) ih)))
    recs (nat_lit 0)

@[expose] noncomputable def signExt (n F : Nat) : Nat :=
  Nat.lor F (Nat.lor (Nat.shiftLeft (Nat.add n (nat_lit 1)) (Nat.mul (nat_lit 32) n))
    (Nat.shiftLeft n (Nat.mul (nat_lit 32) (Nat.add n (nat_lit 1)))))

end CFSG.KC.YModel

end
