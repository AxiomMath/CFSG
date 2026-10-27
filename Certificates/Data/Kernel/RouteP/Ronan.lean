module

public import Certificates.Data.Kernel.RouteP.Geom
public import Certificates.Data.Kernel.Spor.Fi24NetPt

public section

namespace CFSG.KC.RouteP

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24NetPt

@[expose] noncomputable def kvN (a b p : Nat) : Nat :=
  Nat.add (Nat.land (Nat.shiftRight a p) (nat_lit 1))
    (Nat.mul (nat_lit 2) (Nat.land (Nat.shiftRight b p) (nat_lit 1)))

@[expose] noncomputable def eLN (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (z : Int) (N : Nat) : Nat :=
  nIf(Nat.blt N (nat_lit 920808),
    Int.rec (motive := fun _ => Nat)
      (fun m => nIf(Nat.beq m (nat_lit 0), N,
        (fun j p => Nat.add (Nat.mul (nat_lit 3) (ptF (NW j) p))
            (Nat.mod (Nat.add (Nat.mod N (nat_lit 3)) (kvN (KA j) (KB j) p)) (nat_lit 3)))
          (Nat.sub m (nat_lit 1)) (Nat.div N (nat_lit 3))))
      (fun n => (fun q => Nat.add (Nat.mul (nat_lit 3) q)
          (Nat.mod (Nat.add (Nat.mod N (nat_lit 3)) (Nat.mul (nat_lit 2) (kvN (KA n) (KB n) q)))
            (nat_lit 3)))
        (ptR (NW n) (Nat.div N (nat_lit 3)))) z,
    N)

@[expose] noncomputable def ptW (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (w : List Int) (N : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) N (fun z _ ih => strictN ih (eLN NW KA KB z)) w

@[expose] def twd (n : Nat) : Nat → List Int :=
  Nat.rec (motive := fun _ => Nat → List Int) (fun _ => [])
    (fun _ ih c => Int.negSucc (Nat.land c 1) :: ih (Nat.shiftRight c 1)) n

@[expose] noncomputable def pl (R : Nat → Nat) (i : Nat) : Nat :=
  mk3 (R (Nat.mul (nat_lit 3) i)) (R (Nat.add (Nat.mul (nat_lit 3) i) (nat_lit 1)))
    (R (Nat.add (Nat.mul (nat_lit 3) i) (nat_lit 2)))

@[expose] noncomputable def l3S (R : Nat → Nat) : Nat := Nat.lor (pl R 1) (pl R 2)

@[expose] noncomputable def l2S (R : Nat → Nat) : Nat :=
  Nat.land ptsS (Nat.xor ptsS (Nat.land ptsS
    (Nat.lor (Nat.lor (single 0) (Nat.lor (single 1) (single 2))) (Nat.lor (pl R 0) (l3S R)))))

@[expose] noncomputable def tgt (R : Nat → Nat) (g : Nat) : Nat :=
  nIf(Nat.beq g 0, Nat.land (pl R 0) (pl R 3),
  nIf(Nat.beq g 1, Nat.land (pl R 3) (l2S R),
  nIf(Nat.beq g 2, Nat.land (pl R 4) (l2S R),
  nIf(Nat.beq g 3, Nat.land (pl R 4) (l3S R),
  nIf(Nat.beq g 4, Nat.land (pl R 5) (l2S R), Nat.land (pl R 5) (l3S R))))))

@[expose] noncomputable def src (R : Nat → Nat) (g : Nat) : Nat :=
  nIf(Nat.beq g 1, Nat.land (pl R 0) (pl R 3),
  nIf(Nat.beq g 3, Nat.land (pl R 4) (l2S R), Nat.land (pl R 5) (l2S R)))

@[expose] noncomputable def eCode (r : Nat) : Nat := Nat.land r (nat_lit 18446744073709551615)

@[expose] noncomputable def eLen (r : Nat) : Nat := Nat.land (Nat.shiftRight r (nat_lit 64)) (nat_lit 255)

@[expose] noncomputable def eU (r : Nat) : Nat := Nat.land (Nat.shiftRight r (nat_lit 72)) (nat_lit 16777215)

@[expose] noncomputable def ePar (r : Nat) : Nat := Nat.land (Nat.shiftRight r (nat_lit 96)) (nat_lit 65535)

@[expose] noncomputable def eGrp (r : Nat) : Nat := Nat.land (Nat.shiftRight r (nat_lit 112)) (nat_lit 255)

@[expose] noncomputable def baseOK (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (zg : List Int)
    (R : Nat → Nat) (i : Nat) : Bool :=
  bIf(Nat.blt i (nat_lit 3),
    Nat.beq (pl R i) (zS NW KA KB zg ([1, 3, 4].getD i 0)),
    Nat.beq (pl R i) (imgW NW KA KB (gMW (Nat.sub i (nat_lit 1))) (pl R 0)))

@[expose] noncomputable def entOK (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (R E : Nat → Nat)
    (e : Nat) : Bool :=
  letB (E e) fun r => (fun w =>
    andB (Nat.beq (ptW NW KA KB w 0) (eU r))
      (Nat.beq (pl R (Nat.add e (nat_lit 6))) (Nat.land (imgW NW KA KB w (pl R 0)) (tgt R (eGrp r)))))
    (twd (eLen r) (eCode r))

@[expose] noncomputable def unionE (R E : Nat → Nat) (pt : Bool) (lo n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i ih => Nat.lor (Nat.lor (pl R (Nat.add (Nat.add lo i) (nat_lit 6)))
      (Bool.rec (motive := fun _ => Nat) 0 (single (eU (E (Nat.add lo i)))) pt)) ih) n

@[expose] noncomputable def spanPt (R E : Nat → Nat) (g lo e : Nat) : Bool :=
  letB (E e) fun r => letB (ePar r) fun p =>
    orB (andB (Nat.beq p e) (memP (tgt R g) (eU r)))
      (andB (Nat.ble lo p) (andB (Nat.blt p e) (memP (pl R (Nat.add p (nat_lit 6))) (eU r))))

@[expose] noncomputable def grpOK (R E : Nat → Nat) (g lo hi : Nat) : Bool :=
  letB (Nat.sub hi lo) fun n => letB (tgt R g) fun V =>
  andB (allI n fun i => letB (Nat.add lo i) fun e => andB (Nat.beq (eGrp (E e)) g)
      (Bool.rec (motive := fun _ => Bool) (spanPt R E g lo e) (memP (src R g) (eU (E e)))
        (Nat.beq (Nat.land g 1) 1)))
    (Nat.beq (Nat.land V (unionE R E (Nat.beq (Nat.land g 1) 0) lo n)) V)

@[expose] noncomputable def n4OK (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (R : Nat → Nat) (w : List Int) :
    Bool :=
  letB (imgW NW KA KB w (pl R 0)) fun H => Nat.beq (Nat.land H (l3S R)) H

@[expose] def h4P : List Int := [-30, -31, -32, -33, -34, -35, -36, -39]

@[expose] def h4L : List Int := [-7, -8, -9, -88, -89, -90, -91, -92, -93, -94, -97]

@[expose] noncomputable def h4Pt (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (G X : Nat) (z : Int) : Bool :=
  andB (Nat.beq (eLN NW KA KB z 0) 0)
    (letB (eLN NW KA KB z 1479) fun v => orB (Nat.beq v 1479) (andB (memP G v) (memP X v)))

@[expose] noncomputable def h4OK (NWP : Nat → Nat → Nat) (KAP KBP : Nat → Nat) (NWO : Nat → Nat → Nat)
    (KAO KBO : Nat → Nat) (NWC : Nat → Nat → Nat) (KAC KBC : Nat → Nat) (R : Nat → Nat) : Bool :=
  letB (pl R 0) fun G => letB (imgW NWP KAP KBP (gMW 1) G) fun X =>
  andB (andB (List.rec (motive := fun _ => Bool) true (fun z _ ih => andB (h4Pt NWO KAO KBO G X z) ih)
      [-7, -8, -9])
    (List.rec (motive := fun _ => Bool) true (fun z _ ih => andB (h4Pt NWP KAP KBP G X z) ih) h4P))
    (Nat.beq (closeS NWC KAC KBC h4L 7 (single 1479)) G)

end CFSG.KC.RouteP

end
