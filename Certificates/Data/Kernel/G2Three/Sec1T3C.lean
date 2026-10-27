module

public import Certificates.Data.Kernel.G2Three.Sec1T3A

public section

namespace CFSG.KD.G2Three.Sec1T3

open CFSG.KC.Loop

@[expose] noncomputable def entL (L k : Nat) : Nat := fld(L, Nat.mul 128 k, M128)

@[expose] noncomputable def rgAt (RG k : Nat) : Nat := fld(RG, Nat.mul 32 k, 4294967295)

@[expose] noncomputable def genAt (g t : Nat) : Nat := fld(g, Nat.add 3 (Nat.mul 7 t), 127)

@[expose] noncomputable def subM (X Y : Nat) : Bool := Nat.beq (Nat.land X Y) X

@[expose] noncomputable def orBelow (m hi : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun h ih => Nat.lor (
    Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
      Nat.lor ((fun i => nIf(Nat.blt i m, f i, 0)) (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64) ih) hi

@[expose] noncomputable def maxN (a b : Nat) : Nat := nIf(Nat.ble a b, b, a)

@[expose] noncomputable def maxBelow (m hi : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun h ih => maxN (
    Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
      maxN ((fun i => nIf(Nat.blt i m, f i, 0)) (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64) ih) hi

@[expose] noncomputable def cenS (P C X : Nat) (gs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) X (fun g _ acc => cenE P C acc g) gs

@[expose] noncomputable def cenR (P C X g : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) X (fun t acc => cenE P C acc (genAt g t)) (Nat.land g 7)

@[expose] noncomputable def upS (P C V X Zm : Nat) (gs : List Nat) : Nat :=
  strictN X fun X => strictN Zm fun Zm =>
    Nat.rec (motive := fun _ => Nat) 0 (fun i acc =>
      nIf(bAnd(hasB X i, List.rec (motive := fun _ => Bool) true
          (fun g _ ih => bAnd(hasB Zm (commE P C V i g), ih)) gs),
        Nat.lor acc (Nat.shiftLeft 1 i), acc)) 128

@[expose] noncomputable def commSetM (P C V X Y : Nat) : Nat :=
  strictN X fun X => strictN Y fun Y =>
    Nat.rec (motive := fun _ => Nat) 0 (fun x acc => nIf(hasB X x, Nat.lor acc
      (Nat.rec (motive := fun _ => Nat) 0 (fun y acc2 =>
        nIf(hasB Y y, Nat.lor acc2 (Nat.shiftLeft 1 (commE P C V x y)), acc2)) 128), acc)) 128

@[expose] noncomputable def stepM (C m M : Nat) : Nat :=
  strictN M fun M => Nat.rec (motive := fun _ => Nat) M (fun g acc =>
    nIf(hasB m g, Nat.lor acc (imgR (rowT C g) M), acc)) 128

@[expose] noncomputable def closM (C m R : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 1 (fun _ acc => strictN acc (stepM C m)) R

@[expose] noncomputable def closMOK (C m R : Nat) : Bool :=
  strictB (closM C m R) fun M => Nat.beq (stepM C m M) M

@[expose] noncomputable def conjM (P C V s X : Nat) : Nat :=
  strictN X fun X => strictN (rowT P s) fun rx => strictN (rowT C (atR V s)) fun cv =>
    Nat.rec (motive := fun _ => Nat) 0 (fun i acc =>
      nIf(hasB X i, Nat.lor acc (Nat.shiftLeft 1 (conjR rx cv i)), acc)) 128

@[expose] noncomputable def normM (P C V X N : Nat) : Bool :=
  strictB X fun X => strictB N fun N =>
    allBelow 128 2 fun x => bIf(hasB X x, Nat.beq (conjM P C V x N) N, true)

@[expose] noncomputable def secEK (P C V Q X N f : Nat) : Bool :=
  bAnd(subM N X, bAnd(normM P C V X N, bAnd(subM (imgR Q X) N,
    Nat.beq (pop X) (Nat.mul f (pop N)))))

@[expose] noncomputable def secC (Q L m X N : Nat) : Nat :=
  strictN X fun X => strictN N fun N => orBelow m 7 fun k => strictN (entL L k) fun K =>
    nIf(bAnd(subM N K, bAnd(subM K X, subM (imgR Q K) N)), Nat.shiftLeft 1 k, 0)

@[expose] noncomputable def maxIdx (L Cm m : Nat) : Nat :=
  strictN Cm fun Cm => orBelow m 7 fun k => nIf(hasB Cm k, strictN (entL L k) fun K =>
    nIf(allBelow m 7 fun k' => bIf(hasB Cm k', strictB (entL L k') fun K' =>
        bIf(subM K K', Nat.beq K K', true), true), Nat.shiftLeft 1 k, 0), 0)

@[expose] noncomputable def eaMaxK (Q L m X N k1 k2 : Nat) : Bool :=
  bAnd(Bool.not' (Nat.beq k1 k2),
    Nat.beq (maxIdx L (secC Q L m X N) m) (Nat.lor (Nat.shiftLeft 1 k1) (Nat.shiftLeft 1 k2)))

@[expose] noncomputable def abR (P C V g N : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun t ih => bAnd(
    Nat.rec (motive := fun _ => Bool) true (fun u ih2 =>
      bAnd(hasB N (commE P C V (genAt g t) (genAt g u)), ih2)) (Nat.land g 7), ih)) (Nat.land g 7)

@[expose] noncomputable def jC (P C V L RG m X N : Nat) : Nat :=
  strictN X fun X => strictN N fun N => orBelow m 7 fun k => strictN (entL L k) fun K =>
    nIf(bAnd(subM N K, bAnd(subM K X, abR P C V (rgAt RG k) N)), Nat.shiftLeft 1 k, 0)

@[expose] noncomputable def omN (Q K N : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc =>
    nIf(bAnd(hasB K i, hasB N (atR Q i)), Nat.succ acc, acc)) 128

@[expose] noncomputable def j0U (P C V L RG m X : Nat) : Nat :=
  strictN (jC P C V L RG m X 1) fun Cm =>
    strictN (maxBelow m 7 fun k => nIf(hasB Cm k, pop (entL L k), 0)) fun mx =>
      orBelow m 7 fun k => nIf(hasB Cm k, strictN (entL L k) fun K =>
        nIf(Nat.beq (pop K) mx, K, 0), 0)

@[expose] noncomputable def joinK (C U R T : Nat) : Bool :=
  strictB U fun U => bAnd(closMOK C U R, Nat.beq (closM C U R) T)

@[expose] noncomputable def pRankK (Q L m X : Nat) : Nat :=
  strictN X fun X => maxBelow m 7 fun k => strictN (entL L k) fun K =>
    nIf(bAnd(subM K X, Nat.beq (imgR Q K) 1), pop K, 0)

@[expose] noncomputable def cycK (P X : Nat) : Bool :=
  strictB X fun X => strictB (Nat.shiftRight (pop X) 1) fun e =>
    Nat.rec (motive := fun _ => Bool) false (fun i ih =>
      bIf(bAnd(hasB X i, Bool.not' (Nat.beq (powE P i e) 0)), true, ih)) 128

@[expose] noncomputable def q8M (u v : Nat) : Nat :=
  (fun i j => nIf(Nat.blt u 4,
      nIf(Nat.blt v 4, Nat.mod (Nat.add i j) 4, Nat.add 4 (Nat.mod (Nat.sub (Nat.add j 4) i) 4)),
      nIf(Nat.blt v 4, Nat.add 4 (Nat.mod (Nat.add i j) 4),
        Nat.mod (Nat.add 2 (Nat.sub (Nat.add j 4) i)) 4)))
    (Nat.mod u 4) (Nat.mod v 4)

@[expose] noncomputable def q8K (P r s Qm : Nat) : Bool :=
  bAnd(allBelow 64 1 fun uv => (fun u v =>
      Nat.beq (d8I P r s (q8M u v)) (mulE P (d8I P r s u) (d8I P r s v)))
    (Nat.shiftRight uv 3) (Nat.land uv 7),
  bAnd(Nat.beq (Nat.rec (motive := fun _ => Nat) 0
      (fun k acc => Nat.lor acc (Nat.shiftLeft 1 (d8I P r s k))) 8) Qm,
    Nat.beq (pop Qm) 8))

@[expose] noncomputable def z4M (c d : Nat) : Nat :=
  Nat.add (Nat.mul 4 (Nat.mod (Nat.add (Nat.shiftRight c 2) (Nat.shiftRight d 2)) 4))
    (Nat.mod (Nat.add (Nat.land c 3) (Nat.land d 3)) 4)

@[expose] noncomputable def z4I (P u v c : Nat) : Nat :=
  mulE P (powE P u (Nat.shiftRight c 2)) (powE P v (Nat.land c 3))

@[expose] noncomputable def z4K (P u v Jm : Nat) : Bool :=
  bAnd(allBelow 256 4 fun cd => (fun c d =>
      Nat.beq (z4I P u v (z4M c d)) (mulE P (z4I P u v c) (z4I P u v d)))
    (Nat.shiftRight cd 4) (Nat.land cd 15),
  bAnd(Nat.beq (Nat.rec (motive := fun _ => Nat) 0
      (fun c acc => Nat.lor acc (Nat.shiftLeft 1 (z4I P u v c))) 16) Jm,
    Nat.beq (pop Jm) 16))

@[expose] noncomputable def invertK (P C V h X : Nat) : Bool :=
  strictB X fun X => allBelow 128 2 fun y =>
    bIf(hasB X y, Nat.beq (conjR (rowT P h) (rowT C (atR V h)) y) (atR V y), true)

@[expose] noncomputable def outB (H g : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun t ih =>
    bIf(Bool.not' (hasB H (genAt g t)), true, ih)) (Nat.land g 7)

@[expose] noncomputable def rgK (L RG m : Nat) : Bool :=
  allBelow m 7 fun k => (fun g => bAnd(Nat.ble (Nat.land g 7) 4, gensIn (entL L k) g)) (rgAt RG k)

@[expose] noncomputable def rgAllK (L OR RG m lo w : Nat) : Bool :=
  allBelow w 7 fun l => (fun k => strictB (entL L k) fun K => strictB (rgAt RG k) fun g =>
    strictB (ordAt OR k) fun ok => allBelow m 7 fun h =>
      bIf(Nat.beq (Nat.mul 2 (ordAt OR h)) ok, strictB (entL L h) fun H =>
        bIf(subM H K, outB H g, true), true)) (Nat.add lo l)

@[expose] noncomputable def f14aK (P C V Q a1 b1 a2 b2 h0 R : Nat) : Bool :=
  (fun gs => bAnd(closOK C gs R, bAnd(closOK C [atR Q b1] R, bAnd(closOK C [b1, b2] R,
    strictB (closK C gs R) fun S => strictB (closK C [atR Q b1] R) fun Zm =>
    bAnd(Nat.beq (cenS P C S gs) Zm, strictB (upS P C V S Zm gs) fun Z2 =>
    strictB (commSetM P C V S S) fun Cs =>
    bAnd(closMOK C Cs R, bAnd(Nat.beq (closM C Cs R) Z2,
    bAnd(Nat.beq Z2 (closK C [b1, b2] R), secEK P C V Q S Z2 8))))))))
    [a1, b1, a2, b2, h0]

@[expose] noncomputable def f14bK (P C V Q L RG m a1 b1 a2 b2 h0 R : Nat) : Bool :=
  bAnd(closOK C [a1, b1] R, bAnd(closOK C [a2, b2] R, bAnd(closOK C [a1, b1, a2, b2] R,
  bAnd(closOK C [a1, b1, a2, b2, h0] R, bAnd(closOK C [atR Q b1] R,
  strictB (closK C [a1, b1] R) fun A1 => strictB (closK C [a2, b2] R) fun A2 =>
  strictB (closK C [a1, b1, a2, b2] R) fun A => strictB (closK C [a1, b1, a2, b2, h0] R) fun S =>
  strictB (closK C [atR Q b1] R) fun Zm =>
  bAnd(q8K P a1 b1 A1, bAnd(q8K P a2 b2 A2, bAnd(Nat.beq (cenS P C A2 [a1, b1]) A2,
  bAnd(Nat.beq (prodM C A1 A2) A, bAnd(Nat.beq (Nat.land A1 A2) Zm,
  bAnd(Nat.beq (pop A) 32, strictB (cenS P C A [a1, b1, a2, b2]) fun ZA =>
  bAnd(Nat.beq ZA Zm, bAnd(Nat.beq (pop ZA) 2, bAnd(subM (imgR Q A) ZA,
  strictB (commSetM P C V A A) fun Cs => bAnd(closMOK C Cs R, bAnd(Nat.beq (closM C Cs R) ZA,
  allBelow m 7 fun k => strictB (entL L k) fun K =>
    bIf(bAnd(subM K S, Nat.beq (pop K) 32), strictB (cenR P C K (rgAt RG k)) fun ZK =>
      bIf(bAnd(Nat.beq (pop ZK) 2, subM (imgR Q K) ZK), Nat.beq K A, true), true)))))))))))))))))

@[expose] noncomputable def f14cK (P C V Q L RG m a1 b1 a2 b2 h0 R : Nat) : Bool :=
  (fun gs gB b1b2 a1a2h0 => bAnd(closOK C gs R, bAnd(closOK C [atR Q b1] R, bAnd(closOK C gB R,
  bAnd(closOK C [b1b2, atR Q b1] R, bAnd(closOK C [b1, a1a2h0] R,
  strictB (closK C gs R) fun S => strictB (closK C [atR Q b1] R) fun Zm =>
  strictB (upS P C V S Zm gs) fun Z2 => strictB (cenE P C S b1b2) fun Bm =>
  strictB (closK C [b1, a1a2h0] R) fun J =>
  bAnd(Nat.beq Bm (closK C gB R), strictB (cenS P C Bm gB) fun ZB =>
  bAnd(Nat.beq ZB (closK C [b1b2, atR Q b1] R),
  bAnd(closMOK C (involM Q Z2) R, bAnd(Nat.beq ZB (closM C (involM Q Z2) R),
  bAnd(Nat.beq (pop Bm) 32, bAnd(Bool.not' (cycK P ZB),
  bAnd(allBelow m 7 (fun k => strictB (entL L k) fun K =>
    bIf(bAnd(subM K S, bAnd(Nat.beq (pop K) 32, Bool.not' (cycK P (cenR P C K (rgAt RG k))))),
      Nat.beq K Bm, true)),
  bAnd(joinK C (j0U P C V L RG m S) R J, bAnd(joinK C (j0U P C V L RG m Bm) R J,
  bAnd(z4K P b1 a1a2h0 J, bAnd(closMOK C (involM Q J) R, bAnd(Nat.beq ZB (closM C (involM Q J) R),
    invertK P C V h0 J))))))))))))))))))
    [a1, b1, a2, b2, h0] [mulE P a1 a2, b1, b2, h0] (mulE P b1 b2) (mulE P (mulE P a1 a2) h0)

@[expose] noncomputable def f14dK (P C V Q L m a1 b1 a2 b2 h0 kE kF R : Nat) : Bool :=
  (fun gB b1b2 a1a2 z => bAnd(closOK C [a1, b1, a2, b2] R, bAnd(closOK C [a1, b1, a2, b2, h0] R,
  bAnd(closOK C [b1b2, mulE P (mulE P a1 b1) a2, z] R, bAnd(closOK C [a1a2, b1b2, z] R,
  bAnd(closOK C gB R,
  strictB (closK C [a1, b1, a2, b2] R) fun A => strictB (closK C [a1, b1, a2, b2, h0] R) fun S =>
  strictB (cenE P C S b1b2) fun Bm => strictB (closK C [b1b2, mulE P (mulE P a1 b1) a2, z] R)
    fun E => strictB (closK C [a1a2, b1b2, z] R) fun F => strictB (Nat.land A Bm) fun AB =>
  bAnd(Nat.beq Bm (closK C gB R), bAnd(Nat.beq (prodM C E F) AB, bAnd(permB P C E F,
  bAnd(z2d8K P C Q AB b1b2 b1 a1a2 R, bAnd(eaMaxK Q L m AB 1 kE kF,
  bAnd(Nat.beq (entL L kE) E, bAnd(Nat.beq (entL L kF) F,
    Nat.beq (Nat.land E F) (cenS P C Bm gB))))))))))))))
    [mulE P a1 a2, b1, b2, h0] (mulE P b1 b2) (mulE P a1 a2) (atR Q b1)

@[expose] noncomputable def f14eK (P C V Q L m a1 b1 a2 b2 h0 kA kB kZ R : Nat) : Bool :=
  (fun gs gB b1b2 z => bAnd(closOK C gs R, bAnd(closOK C [a1, b1, a2, b2] R, bAnd(closOK C gB R,
  bAnd(closOK C [mulE P a1 a2, b1b2, z] R, bAnd(closOK C [z] R, bAnd(closOK C [b1, b2, h0] R,
  bAnd(closOK C [h0] R,
  strictB (closK C gs R) fun S => strictB (closK C [a1, b1, a2, b2] R) fun A =>
  strictB (cenE P C S b1b2) fun Bm => strictB (closK C [mulE P a1 a2, b1b2, z] R) fun F =>
  strictB (closK C [z] R) fun Zm => strictB (upS P C V S Zm gs) fun Z2 =>
  strictB (closK C [b1, b2, h0] R) fun Z2h => strictB (closK C [h0] R) fun H0 =>
  bAnd(Nat.beq Bm (closK C gB R), bAnd(normM P C V S F, bAnd(eaMaxK Q L m S F kA kB,
  bAnd(Nat.beq (entL L kA) A, bAnd(Nat.beq (entL L kB) Bm, bAnd(normM P C V S Zm,
  bAnd(eaMaxK Q L m S Zm kA kZ, bAnd(Nat.beq (entL L kZ) Z2h, bAnd(Nat.beq (prodM C Z2 H0) Z2h,
  bAnd(permB P C Z2 H0, z2d8K P C Q Z2h b1b2 b1 h0 R))))))))))))))))))
    [a1, b1, a2, b2, h0] [mulE P a1 a2, b1, b2, h0] (mulE P b1 b2) (atR Q b1)

@[expose] noncomputable def ys14 (Y0 Y1 Y2 Y3 Y4 j : Nat) : Nat :=
  nIf(Nat.beq j 0, Y0, nIf(Nat.beq j 1, Y1, nIf(Nat.beq j 2, Y2, nIf(Nat.beq j 3, Y3, Y4))))

@[expose] noncomputable def wIdx (ws : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ acc =>
    Nat.lor (Nat.shiftLeft 1 (Nat.land w 511)) acc) ws

@[expose] noncomputable def f14fK (P C V Q L m a1 b1 a2 b2 h0 R : Nat) (ws : List Nat) : Bool :=
  (fun gs gB b1b2 z a1b2 => bAnd(closOK C gs R, bAnd(closOK C gB R,
  bAnd(closOK C [b1b2, mulE P (mulE P a1 b1) a2, z] R, bAnd(closOK C [mulE P a1 a2, b1b2, z] R,
  bAnd(closOK C [h0] R, bAnd(closOK C [a1b2, mulE P b1 a2, z] R,
  bAnd(closOK C [a1b2, mulE P (mulE P a1 b1) a2, z] R,
  strictB (closK C gs R) fun S => strictB (cenE P C S b1b2) fun Bm =>
  strictB (cenS P C Bm gB) fun ZB => strictB (closK C [h0] R) fun H0 =>
  strictB (closK C [b1b2, mulE P (mulE P a1 b1) a2, z] R) fun Y0 =>
  strictB (closK C [mulE P a1 a2, b1b2, z] R) fun Y1 => strictB (prodM C ZB H0) fun Y2 =>
  strictB (closK C [a1b2, mulE P b1 a2, z] R) fun Y3 =>
  strictB (closK C [a1b2, mulE P (mulE P a1 b1) a2, z] R) fun Y4 =>
  strictB (maxIdx L (secC Q L m S 1) m) fun Mx =>
  bAnd(Nat.beq Bm (closK C gB R), bAnd(permB P C ZB H0,
  bAnd(Nat.beq (sumBelow m 7 fun k => nIf(hasB Mx k, 1, 0)) 8, bAnd(Nat.beq (wIdx ws) Mx,
  List.rec (motive := fun _ => Bool) true (fun w _ ih => bAnd(
      (fun s => bAnd(hasB S s, Nat.beq (entL L (Nat.land w 511))
        (conjM P C V s (ys14 Y0 Y1 Y2 Y3 Y4 (Nat.shiftRight w 16))))) (fld(w, 9, 127)), ih))
    ws))))))))))))
    [a1, b1, a2, b2, h0] [mulE P a1 a2, b1, b2, h0] (mulE P b1 b2) (atR Q b1) (mulE P a1 b2)

@[expose] noncomputable def f14gK (P C V Q L m a1 b1 a2 b2 h0 R : Nat) : Bool :=
  bAnd(closOK C [a1, b1, a2, b2, h0] R, bAnd(closOK C [a1, b1, a2, b2] R,
  bAnd(closOK C [atR Q b1] R,
  bAnd(Nat.beq (pRankK Q L m (closK C [a1, b1, a2, b2, h0] R)) 8,
    secEK P C V Q (closK C [a1, b1, a2, b2] R) (closK C [atR Q b1] R) 16))))

end CFSG.KD.G2Three.Sec1T3
