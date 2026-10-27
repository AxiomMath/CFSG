module

public import Certificates.Data.Kernel.AS35QTS.Planes

public section

namespace CFSG.KC.AS35QTS

open CFSG.KC.F4M3B

@[expose] def mapP {α β : Type} (f : α → β) (X : PL α) : PL β :=
  ⟨f X.e, ⟨f X.a.l0, f X.a.h0, f X.a.l1, f X.a.h1, f X.a.l2, f X.a.h2⟩,
    ⟨f X.r0.l0, f X.r0.h0, f X.r0.l1, f X.r0.h1, f X.r0.l2, f X.r0.h2⟩,
    ⟨f X.r1.l0, f X.r1.h0, f X.r1.l1, f X.r1.h1, f X.r1.l2, f X.r1.h2⟩,
    ⟨f X.r2.l0, f X.r2.h0, f X.r2.l1, f X.r2.h1, f X.r2.l2, f X.r2.h2⟩⟩

@[expose] noncomputable def lenR (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) L

@[expose] def ones (n : Nat) : Nat := Nat.sub (Nat.pow 2 n) 1

@[expose] noncomputable def cmp (L : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun c _ ih => Nat.add (bitN p c) (Nat.mul 2 ih)) L

@[expose] noncomputable def cmpP (X : PL Nat) (L : List Nat) : PL Nat := mapP (cmp L) X

@[expose] noncomputable def pairA (na nb p : Nat) : Nat :=
  blk nb (fun i => Nat.mul (bitN p i) (ones nb)) na

@[expose] noncomputable def pairB (na nb p : Nat) : Nat := blk nb (fun _ => p) na

@[expose] def commP (t : Nat) (X C : PL Nat) : Nat :=
  mulK (natOps t) frcN X C fun A => mulK (natOps t) frcN C X fun B => eqP (natOps t) A B

@[expose] noncomputable def anyComm (t : Nat) (X X' : PL Nat) (R : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun r _ ih => Nat.lor (commP t X (atLane t X' r)) ih) R

@[expose] noncomputable def allI (L : List Nat) (f : Nat → Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih j => Bool.and' (f j x) (ih (Nat.succ j))) L 0

@[expose] noncomputable def allI2 (L M : List Nat) (f : Nat → Nat → Nat → Bool) : Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Bool) (fun _ _ => true)
    (fun x _ ih M j => List.rec (motive := fun _ => Bool) false
      (fun y rest _ => Bool.and' (f j x y) (ih rest (Nat.succ j))) M) L M 0

@[expose] noncomputable def hitK (t : Nat) (Y T : PL Nat) (n : Nat) : PL Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => PL Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih P acc => mulK (natOps t) frcN P Y fun P' =>
      frcN (Nat.lor acc (eqP (natOps t) P T)) fun acc' => ih P' acc') n

@[expose] def laneT : Nat := 41589

@[expose] noncomputable def ilOK (G IL : List Nat) : Bool :=
  Bool.and' (incB 82944 IL) (frc allT fun tA => lanesK G fun X =>
    mulK (natOps tA) frc X X fun Q => Nat.beq (invM tA X Q) (ind IL))

@[expose] noncomputable def qpowOK (G : List Nat) : Bool :=
  frc allT fun tA => lanesK G fun X => bindP (cst tA ixE) fun E =>
    mulK (natOps tA) frc E X fun P1 => mulK (natOps tA) frc P1 X fun P2 =>
    mulK (natOps tA) frc P2 X fun P3 => mulK (natOps tA) frc P3 X fun P4 =>
      Nat.beq (Nat.land (isI3 (natOps tA) X) (bnot (natOps tA) (eqP (natOps tA) P4 E))) 0

@[expose] noncomputable def rootOK (G IL R : List Nat) : Bool :=
  Bool.and' (incB 82944 R) <| frc allT fun tA => lanesK G fun X => mulK (natOps tA) frc X X fun Q =>
    Bool.and' (Nat.beq (Nat.land (ind R) (bnot (natOps tA)
        (Nat.land (isI3 (natOps tA) X) (eqP (natOps tA) Q (cst tA ixT))))) 0)
      (frc (ones (lenR IL)) fun ti => bindP (cmpP X IL) fun Xi =>
        Nat.beq (Nat.land (bnot (natOps ti) (isI3 (natOps ti) Xi))
          (bnot (natOps ti) (anyComm ti Xi X R))) 0)

@[expose] noncomputable def invOK (G IL S INV : List Nat) : Bool :=
  frc allT fun tA => lanesK G fun X =>
    Bool.and' (Nat.beq (eqP (natOps 1) (atLane 1 X laneT) (cst 1 ixT)) 1)
    (frc (Nat.lor (Nat.shiftLeft 1 laneT) (ind S)) fun D =>
    Bool.and' (allI INV fun _ w =>
        let c := Nat.land w (ones 17)
        let a := Nat.land (Nat.shiftRight w 17) (ones 17)
        let b := Nat.shiftRight w 34
        Bool.and' (Nat.beq (bitN D a) 1) (Bool.and' (Nat.beq (bitN D b) 1)
          (Bool.and' (Bool.not' (Nat.beq a b))
            (Bool.and' (Nat.beq (commP 1 (atLane 1 X a) (atLane 1 X b)) 1)
              (mulK (natOps 1) frc (atLane 1 X a) (atLane 1 X b) fun P =>
                Nat.beq (eqP (natOps 1) P (atLane 1 X c)) 1)))))
      (Nat.beq (Nat.land (ind IL) (bnot (natOps tA) (Nat.lor D
        (List.rec (motive := fun _ => Nat) 0
          (fun w _ ih => Nat.lor (Nat.shiftLeft 1 (Nat.land w (ones 17))) ih) INV)))) 0))

@[expose] noncomputable def classOK (G S CLS : List Nat) : Bool :=
  lanesK G fun X => List.rec (motive := fun _ => Bool) false (fun t0 _ _ =>
    allI2 S CLS fun _ s m => Bool.and' (Nat.blt m 82944) <|
      mulK (natOps 1) frc (atLane 1 X m) (atLane 1 X t0) fun A =>
      mulK (natOps 1) frc (atLane 1 X s) (atLane 1 X m) fun B => Nat.beq (eqP (natOps 1) A B) 1) S

@[expose] noncomputable def ordOK (G S : List Nat) : Bool :=
  lanesK G fun X => frc (lenR (laneT :: S)) fun n => frc (ones (Nat.mul n n)) fun tp =>
    bindP (mapP (fun p => pairA n n (cmp (laneT :: S) p)) X) fun A =>
    bindP (mapP (fun p => pairB n n (cmp (laneT :: S) p)) X) fun B =>
    bindP (cst tp ixE) fun E =>
    mulK (natOps tp) frc A B fun Y => mulK (natOps tp) frc Y Y fun Y2 =>
    mulK (natOps tp) frc Y2 Y fun Y3 =>
      Nat.beq (bor (natOps tp) (eqP (natOps tp) Y2 E) (eqP (natOps tp) Y3 E)) tp

@[expose] def packP (X : PL Nat) : Nat :=
  Nat.lor (Nat.shiftLeft X.e 24) (Nat.lor (Nat.shiftLeft X.a.l0 22) (Nat.lor
    (Nat.shiftLeft X.a.h0 23) (Nat.lor (Nat.shiftLeft X.a.l1 20) (Nat.lor (Nat.shiftLeft X.a.h1 21)
    (Nat.lor (Nat.shiftLeft X.a.l2 18) (Nat.lor (Nat.shiftLeft X.a.h2 19) (Nat.lor
    (Nat.shiftLeft X.r0.l0 16) (Nat.lor (Nat.shiftLeft X.r0.h0 17) (Nat.lor
    (Nat.shiftLeft X.r0.l1 14) (Nat.lor (Nat.shiftLeft X.r0.h1 15) (Nat.lor
    (Nat.shiftLeft X.r0.l2 12) (Nat.lor (Nat.shiftLeft X.r0.h2 13) (Nat.lor
    (Nat.shiftLeft X.r1.l0 10) (Nat.lor (Nat.shiftLeft X.r1.h0 11) (Nat.lor
    (Nat.shiftLeft X.r1.l1 8) (Nat.lor (Nat.shiftLeft X.r1.h1 9) (Nat.lor
    (Nat.shiftLeft X.r1.l2 6) (Nat.lor (Nat.shiftLeft X.r1.h2 7) (Nat.lor
    (Nat.shiftLeft X.r2.l0 4) (Nat.lor (Nat.shiftLeft X.r2.h0 5) (Nat.lor
    (Nat.shiftLeft X.r2.l1 2) (Nat.lor (Nat.shiftLeft X.r2.h1 3) (Nat.lor
    (Nat.shiftLeft X.r2.l2 0) (Nat.shiftLeft X.r2.h2 1))))))))))))))))))))))))

@[expose] def prodC (X : PL Nat) (a b : Nat) : Nat :=
  mulK (natOps 1) frcN (atLane 1 X a) (atLane 1 X b) packP

@[expose] noncomputable def distProd (X : PL Nat) (L : List Nat) : Bool :=
  allI L fun i a => allI L fun j b => allI L fun i' a' => allI L fun j' b' =>
    Bool.or' (Nat.beq i j) (Bool.or' (Nat.beq i' j') (Bool.or'
      (Bool.not' (Nat.beq (prodC X a b) (prodC X a' b')))
      (Bool.or' (Bool.and' (Nat.beq i i') (Nat.beq j j'))
        (Bool.and' (Nat.beq i j') (Nat.beq j i')))))

@[expose] noncomputable def take5 (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih n => Nat.rec (motive := fun _ => List Nat) [] (fun m _ => x :: ih m) n) L 5

@[expose] noncomputable def drop5 (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x xs ih n => Nat.rec (motive := fun _ => List Nat) (x :: xs) (fun m _ => ih m) n) L 5

@[expose] noncomputable def lineOK (G S LN CM : List Nat) : Bool :=
  lanesK G fun X => frc (Nat.lor (Nat.shiftLeft 1 laneT) (ind S)) fun D =>
    frc (ones 37) fun t37 => frc (ones 36) fun t36 =>
    bindP (cmpP X (laneT :: S)) fun XD => bindP (cmpP X S) fun XS =>
    List.rec (motive := fun _ => List Nat → List Nat → Nat → Bool) (fun _ _ _ => true)
      (fun t _ ih LNs CMs i => List.rec (motive := fun _ => Bool) false (fun row CMr _ =>
        Bool.and' (ih (drop5 LNs) CMr (Nat.succ i))
        (Bool.and' (incB 82944 (take5 LNs)) (Bool.and' (Nat.beq (lenR (take5 LNs)) 5)
        (Bool.and' (allI (take5 LNs) fun _ a => Bool.and' (Nat.beq (bitN D a) 1)
            (Nat.beq (commP 1 (atLane 1 X t) (atLane 1 X a)) 1))
        (Bool.and' (Nat.beq (CFSG.KC.popcount (commP t37 (atLane t37 X t) XD) 64) 5)
        (Bool.and' (allI (take5 LNs) fun _ a => allI (take5 LNs) fun _ b =>
            Nat.beq (commP 1 (atLane 1 X a) (atLane 1 X b)) 1)
        (Bool.and' (distProd X (take5 LNs))
        (Bool.and' (Nat.beq (commP t36 (atLane t36 X t) XS) row)
        (Bool.and' (allI2 S CM fun j _ row' => Bool.or' (Nat.beq (bitN row j) 0) (Nat.beq row row'))
          (mulK (natOps t37) frc (cst t37 ixT) (atLane t37 X t) fun P =>
            Nat.beq (eqP (natOps t37) P XD) 0)))))))))
        ) CMs) S LN CM 0

@[expose] noncomputable def nzOK (G S IL W : List Nat) : Bool :=
  lanesK G fun X => frc (lenR (laneT :: S)) fun na => frc (lenR W) fun nb =>
    frc (ones (Nat.mul na nb)) fun tp =>
    bindP (mapP (fun p => pairA na nb (cmp (laneT :: S) p)) X) fun A =>
    bindP (mapP (fun p => pairB na nb (cmp W p)) X) fun B =>
    bindP (cst tp ixE) fun E => bindP (cst tp ixT) fun T =>
    mulK (natOps tp) frc A B fun Y => mulK (natOps tp) frc Y Y fun c2 =>
    mulK (natOps tp) frc c2 c2 fun c4 => mulK (natOps tp) frc c4 c4 fun c8 =>
    mulK (natOps tp) frc c8 c8 fun c16 => mulK (natOps tp) frc c16 c16 fun c32 =>
    mulK (natOps tp) frc c32 c32 fun c64 => mulK (natOps tp) frc c64 c8 fun c72 =>
      Bool.and' (Bool.and' (incB 82944 W) (Nat.beq (ind W) (Nat.land (ind IL)
          (Nat.xor (Nat.lor (Nat.shiftLeft 1 laneT) (ind S)) allT))))
      <| Bool.and' (Nat.beq (eqP (natOps tp) c72 E) tp)
        (Nat.beq (CFSG.KC.popcount (hitK tp Y T 72 E 0) 3392) 1188)

@[expose] noncomputable def nwOK (G S W V0 LN : List Nat) : Bool :=
  frc allT fun tA => lanesK G fun X => List.rec (motive := fun _ => Bool) false (fun t0 _ _ =>
    Bool.and' (incB 82944 V0) <|
    Bool.and' (Nat.beq (Nat.land (ind W) (commP tA X (atLane tA X t0))) (ind V0))
    (frc (lenR V0) fun nb => frc (ones (Nat.mul 5 nb)) fun tp =>
    bindP (mapP (fun p => pairA 5 nb (cmp (take5 LN) p)) X) fun A =>
    bindP (mapP (fun p => pairB 5 nb (cmp V0 p)) X) fun B =>
    bindP (cst tp ixE) fun E =>
    mulK (natOps tp) frc (cst tp ixT) (atLane tp X t0) fun T =>
    mulK (natOps tp) frc A B fun Y =>
      Nat.beq (CFSG.KC.popcount (hitK tp Y T 72 E 0) 64) 3)) S

@[expose] noncomputable def swapOK (G S IL CM : List Nat) : Bool :=
  lanesK G fun X => frc (ones (lenR IL)) fun ti => bindP (cmpP X IL) fun V =>
    allI2 S CM fun i p row => allI S fun j p' =>
      Bool.or' (Nat.beq i j) (Bool.or' (Nat.beq (bitN row j) 0)
        (mulK (natOps ti) frc V (atLane ti X p) fun A =>
         mulK (natOps ti) frc (atLane ti X p') V fun B =>
         frc (eqP (natOps ti) A B) fun M =>
           Bool.and' (Nat.beq (CFSG.KC.popcount M 128) 16)
             (allI S fun k q => Bool.or' (Nat.beq k i) (Bool.or' (Nat.beq k j)
               (Bool.or' (Nat.beq (bitN row k) 0)
                 (Nat.beq (Nat.land M (commP ti V (atLane ti X q))) 0))))))

@[expose] noncomputable def centOK (G S : List Nat) : Bool :=
  frc allT fun tA => lanesK G fun X => List.rec (motive := fun _ => Bool) false (fun t0 _ _ =>
    Nat.beq (popP (commP tA X (atLane tA X t0))) 2304) S

@[expose] def gensIx : List Nat := [4260097, 1114369, 327937, 8454401, 5124, 131329]

@[expose] noncomputable def centerOK (G : List Nat) : Bool :=
  frc allT fun tA => lanesK G fun X =>
    Nat.beq (Nat.land (List.rec (motive := fun _ => Nat) tA
        (fun g _ ih => Nat.land (commP tA X (cst tA g)) ih) gensIx)
      (bnot (natOps tA) (Nat.lor (eqP (natOps tA) X (cst tA ixE))
        (eqP (natOps tA) X (cst tA ixT))))) 0

end CFSG.KC.AS35QTS

end
