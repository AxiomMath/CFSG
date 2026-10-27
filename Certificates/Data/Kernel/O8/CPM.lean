module

public import Certificates.Data.Kernel.O8.Core
public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KS CFSG.KS.Raw
open CFSG.KC.Enum (pidn pcomp permOK pg)

@[expose] noncomputable def siftC (n w : Nat) (LR TRI : Nat → Nat) (BP nb g : Nat) : Bool :=
  siftK n w (mask w) (Nat.mul n w) (pidn n w) LR TRI BP nb (nat_lit 0) g

@[expose] noncomputable def pc (n w p q : Nat) : Nat := pcomp n w (mask w) p q

@[expose] noncomputable def sigOK (n w SG : Nat) (PSI UA : Nat → Nat) (R : Nat) (LR TRI : Nat → Nat)
    (BP nb : Nat) : Bool :=
  andB (permOK n w (mask w) (Nat.mul n w) SG SG)
    (andB (Nat.beq (pc n w SG SG) (pidn n w))
      (andB (allN (nat_lit 64) fun y => Nat.beq (pc n w (pc n w SG (PSI y)) SG) (PSI (bvecK R y)))
        (allN (nat_lit 6) fun k => siftC n w LR TRI BP nb (pc n w (pc n w SG (UA k)) SG))))

@[expose] noncomputable def wK (G8 G9 j : Nat) : Nat :=
  nIf(Nat.beq j (nat_lit 0), pidn (nat_lit 360) (nat_lit 9),
    nIf(Nat.beq j (nat_lit 1), G9, nIf(Nat.beq j (nat_lit 2), G8,
      nIf(Nat.beq j (nat_lit 3), pc (nat_lit 360) (nat_lit 9) G8 G9,
        nIf(Nat.beq j (nat_lit 4), pc (nat_lit 360) (nat_lit 9) G8 G8,
          pc (nat_lit 360) (nat_lit 9) (pc (nat_lit 360) (nat_lit 9) G8 G8) G9)))))

@[expose] noncomputable def wIK (I8 I9 j : Nat) : Nat :=
  nIf(Nat.beq j (nat_lit 0), pidn (nat_lit 360) (nat_lit 9),
    nIf(Nat.beq j (nat_lit 1), I9, nIf(Nat.beq j (nat_lit 2), I8,
      nIf(Nat.beq j (nat_lit 3), pc (nat_lit 360) (nat_lit 9) I9 I8,
        nIf(Nat.beq j (nat_lit 4), pc (nat_lit 360) (nat_lit 9) I8 I8,
          pc (nat_lit 360) (nat_lit 9) I9 (pc (nat_lit 360) (nat_lit 9) I8 I8))))))

@[expose] noncomputable def cosetOK (G8 G9 I8 I9 : Nat) (LA TA : Nat → Nat) (BA : Nat)
    (LO TO : Nat → Nat) (BO : Nat) : Bool :=
  andB (allN (nat_lit 6) fun i => andB (permOK (nat_lit 360) (nat_lit 9) (mask (nat_lit 9)) (nat_lit 3240)
      (wK G8 G9 i) (wIK I8 I9 i)) (siftC (nat_lit 360) (nat_lit 9) LA TA BA (nat_lit 7) (wK G8 G9 i)))
    (andB (allN (nat_lit 6) fun i => allN (nat_lit 6) fun j => orB (Nat.beq i j)
        (notB (siftC (nat_lit 360) (nat_lit 9) LO TO BO (nat_lit 7) (pc (nat_lit 360) (nat_lit 9) (wK G8 G9 j) (wIK I8 I9 i)))))
      (andB (notB (siftC (nat_lit 360) (nat_lit 9) LO TO BO (nat_lit 7) (pc (nat_lit 360) (nat_lit 9) G8 G8)))
        (andB (notB (siftC (nat_lit 360) (nat_lit 9) LO TO BO (nat_lit 7)
            (pc (nat_lit 360) (nat_lit 9) (wK G8 G9 (nat_lit 4)) (wK G8 G9 (nat_lit 4)))))
          (andB (allN (nat_lit 4) fun j => Nat.ble (nat_lit 120) (pg (nat_lit 9) (mask (nat_lit 9)) (wK G8 G9 (Nat.add j (nat_lit 2))) (nat_lit 0)))
            (andB (allN (nat_lit 360) fun p => bIf(Nat.blt (pg (nat_lit 9) (mask (nat_lit 9)) G9 p) (nat_lit 120),
                Nat.blt p (nat_lit 120), notB (Nat.blt p (nat_lit 120))))
              (andB (Nat.beq (pc (nat_lit 360) (nat_lit 9) G9 G9) (pidn (nat_lit 360) (nat_lit 9)))
                (andB (Nat.beq (pc (nat_lit 360) (nat_lit 9) (pc (nat_lit 360) (nat_lit 9) G8 (wK G8 G9 (nat_lit 3))) I8) G9)
                  (Nat.beq (pc (nat_lit 360) (nat_lit 9) (pc (nat_lit 360) (nat_lit 9) (wK G8 G9 (nat_lit 4)) (wK G8 G9 (nat_lit 5)))
                    (wIK I8 I9 (nat_lit 4))) G9))))))))

@[expose] noncomputable def minusOK (G : Nat) (LL TL : Nat → Nat) (BL : Nat) : Bool :=
  andB (notB (siftC (nat_lit 136) (nat_lit 8) LL TL BL (nat_lit 7) G))
    (Nat.beq (pc (nat_lit 136) (nat_lit 8) G G) (pidn (nat_lit 136) (nat_lit 8)))

end CFSG.KC.O8

end
