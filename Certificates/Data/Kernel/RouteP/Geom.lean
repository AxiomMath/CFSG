module

public import Certificates.Data.Kernel.RouteP.Mono

public section

namespace CFSG.KC.RouteP

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS

@[expose] noncomputable def allI (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) n

@[expose] def gRoot (i : Nat) : Nat := [0, 1479, 3, 750020, 750100, 1, 2].getD i 0

@[expose] def gRounds (i : Nat) : Nat := [0, 33, 41, 24, 26, 0, 0].getD i 0

@[expose] def gSize (i : Nat) : Nat := [1, 31671, 825792, 31671, 31671, 1, 1].getD i 0

@[expose] def gLev (i : Nat) : Nat := [0, 1, 2, 3, 3, 4, 4].getD i 0

@[expose] def gMW (i : Nat) : List Int :=
  [[],
   [-1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, -2,
    -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1],
   [-2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1,
    -2, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, -2, -2, -1],
   [-1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1,
    -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -2, -1, -2, -2],
   [-2, -2, -1, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1,
    -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, -2,
    -1, -2],
   [-1, -2, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1,
    -2, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -2],
   [-2, -1, -2, -2, -1, -2, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1,
    -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1]].getD i []

@[expose] def gWit (i : Nat) : Nat := [0, 0, 26139, 461406, 456434, 102043, 105581].getD i 0

@[expose] def gWl (i : Nat) : Nat := [0, 0, 1, 2, 2, 4, 3].getD i 0

@[expose] def memP (s N : Nat) : Bool := s.testBit (N % 3 * 524288 + N / 3)

@[expose] noncomputable def lorI (S : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i ih => Nat.lor (S i) ih) n

@[expose] noncomputable def orbSetsOK (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (zg : List Int)
    (S : Nat → Nat) : Bool :=
  andB (allI 7 fun i => andB (closedS NW KA KB zg (S i))
      (Nat.beq (pcount (Nat.land (S i) ptsS)) (gSize i)))
    (andB (allI 7 fun i => allI 7 fun j => orB (Nat.beq i j) (Nat.beq (Nat.land (S i) (S j)) 0))
      (Nat.beq (Nat.land (lorI S 7) ptsS) ptsS))

@[expose] noncomputable def distSetOK (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (S : Nat → Nat)
    (i : Nat) : Bool :=
  letB (imgW NW KA KB (gMW i) (S 1)) fun H =>
    andB (ptOK NW KA KB (gMW i) 0 (gRoot i))
      (andB (allI 7 fun j => orB (Nat.ble (gLev j) (gLev i + 1)) (Nat.beq (Nat.land H (S j)) 0))
        (orB (Nat.beq (gLev i) 0)
          (andB (memP H (gWit i)) (andB (memP (S (gWl i)) (gWit i))
            (Nat.beq (gLev (gWl i) + 1) (gLev i))))))

@[expose] noncomputable def s1SetOK (NWO : Nat → Nat → Nat) (KAO KBO : Nat → Nat) (ag : List Int)
    (S1 A : Nat) : Bool :=
  andB (andB (closedS NWO KAO KBO ag A) (Nat.beq (pcount (Nat.land A ptsS)) 3510))
    (andB (allI 3 fun t => andB (ptOK NWO KAO KBO [((t + 7 : Nat) : Int)] 0 0)
        (ptOK NWO KAO KBO [((t + 7 : Nat) : Int)] 1479 1479))
      (letB (Nat.land (imgS NWO KAO KBO (-10) S1) S1) fun X => Nat.beq (Nat.land X A) X))

@[expose] def sel7 (a0 a1 a2 a3 a4 a5 a6 : Nat) (i : Nat) : Nat := [a0, a1, a2, a3, a4, a5, a6].getD i 0

@[expose] noncomputable def geomCore (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (NWO : Nat → Nat → Nat)
    (KAO KBO : Nat → Nat) (zg ag : List Int) (S : Nat → Nat) (A : Nat) : Bool :=
  andB (orbSetsOK NW KA KB zg S) (andB (allI 7 (distSetOK NW KA KB S)) (s1SetOK NWO KAO KBO ag (S 1) A))

@[expose] noncomputable def zS (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (zg : List Int) (i : Nat) :
    Nat :=
  closeS NW KA KB zg (gRounds i) (single (gRoot i))

@[expose] noncomputable def geomSetOK (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (NWO : Nat → Nat → Nat)
    (KAO KBO : Nat → Nat) (zg ag : List Int) : Bool :=
  letB (zS NW KA KB zg 0) fun a0 => letB (zS NW KA KB zg 1) fun a1 =>
  letB (zS NW KA KB zg 2) fun a2 => letB (zS NW KA KB zg 3) fun a3 =>
  letB (zS NW KA KB zg 4) fun a4 => letB (zS NW KA KB zg 5) fun a5 =>
  letB (zS NW KA KB zg 6) fun a6 => letB (closeS NWO KAO KBO ag 10 (single 99705)) fun A =>
  geomCore NW KA KB NWO KAO KBO zg ag (sel7 a0 a1 a2 a3 a4 a5 a6) A

end CFSG.KC.RouteP

end
