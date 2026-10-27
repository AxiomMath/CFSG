module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.D4Q2K

open CFSG.KC.Enum

@[expose] noncomputable def allPl : Nat := Nat.sub (Nat.pow (nat_lit 2) (nat_lit 65536)) (nat_lit 1)

@[expose] noncomputable def notP (x : Nat) : Nat := Nat.xor allPl x

@[expose] noncomputable def bitPl (b : Nat) : Nat :=
  Nat.mul (Nat.shiftLeft (Nat.sub (Nat.pow (nat_lit 2) (Nat.pow (nat_lit 2) b)) (nat_lit 1))
      (Nat.pow (nat_lit 2) b))
    (Nat.div allPl (Nat.sub (Nat.pow (nat_lit 2) (Nat.pow (nat_lit 2) (Nat.succ b))) (nat_lit 1)))

@[expose] noncomputable def lo (k : Nat) : Nat := bitPl (Nat.mul (nat_lit 2) k)

@[expose] noncomputable def hi (k : Nat) : Nat := bitPl (Nat.succ (Nat.mul (nat_lit 2) k))

@[expose] noncomputable def nz (k : Nat) : Nat := Nat.lor (lo k) (hi k)

@[expose] noncomputable def one (k : Nat) : Nat := Nat.land (lo k) (notP (hi k))

@[expose] noncomputable def m0 (x0 x1 y0 y1 : Nat) : Nat := Nat.xor (Nat.land x0 y0) (Nat.land x1 y1)

@[expose] noncomputable def m1 (x0 x1 y0 y1 : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.land x0 y1) (Nat.land x1 y0)) (Nat.land x1 y1)

@[expose] noncomputable def quadLo : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.xor acc (m0 (lo i) (hi i) (lo (Nat.add i (nat_lit 4))) (hi (Nat.add i (nat_lit 4)))))
    (nat_lit 4)

@[expose] noncomputable def quadHi : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.xor acc (m1 (lo i) (hi i) (lo (Nat.add i (nat_lit 4))) (hi (Nat.add i (nat_lit 4)))))
    (nat_lit 4)

@[expose] noncomputable def hermPl : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => Nat.xor acc (nz k)) (nat_lit 8)

@[expose] noncomputable def zUp (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) allPl (fun j acc => Nat.land acc (notP (nz j))) k

@[expose] noncomputable def normPl : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => Nat.lor acc (Nat.land (zUp k) (one k)))
    (nat_lit 8)

@[expose] noncomputable def ptPl : Nat :=
  Nat.land (Nat.land normPl (notP quadLo)) (Nat.land (notP quadHi) hermPl)

@[expose] noncomputable def plOf (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) p) ih) L

@[expose] noncomputable def incFrom (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun p _ ih c => bAnd(Nat.ble c p, bAnd(Nat.blt p (nat_lit 65536), ih (Nat.succ p)))) L

@[expose] noncomputable def ptK (L : List Nat) : Bool :=
  bAnd(incFrom L (nat_lit 0), Nat.beq (plOf L) ptPl)

@[expose] noncomputable def mulT : Nat := nat_lit 2625168384

@[expose] noncomputable def frobT : Nat := nat_lit 180

@[expose] noncomputable def mulK (a b : Nat) : Nat :=
  Nat.land (Nat.shiftRight mulT (Nat.mul (nat_lit 2) (Nat.add (Nat.mul (nat_lit 4) a) b))) (nat_lit 3)

@[expose] noncomputable def frobK (a : Nat) : Nat :=
  Nat.land (Nat.shiftRight frobT (Nat.mul (nat_lit 2) a)) (nat_lit 3)

@[expose] noncomputable def cdK (v k : Nat) : Nat :=
  Nat.land (Nat.shiftRight v (Nat.mul (nat_lit 2) k)) (nat_lit 3)

@[expose] noncomputable def polarK (u v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.xor acc (Nat.xor (mulK (cdK u i) (cdK v (Nat.add i (nat_lit 4))))
      (mulK (cdK u (Nat.add i (nat_lit 4))) (cdK v i)))) (nat_lit 4)

@[expose] noncomputable def hermK (u v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.xor acc (mulK (cdK u k) (frobK (cdK v k)))) (nat_lit 8)

@[expose] noncomputable def adjK (u v : Nat) : Bool :=
  bAnd(Bool.rec (motive := fun _ => Bool) true false (Nat.beq u v),
    bAnd(Nat.beq (polarK u v) (nat_lit 0), Nat.beq (hermK u v) (nat_lit 0)))

@[expose] noncomputable def packL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Nat.lor p (Nat.shiftLeft ih (nat_lit 16))) L

@[expose] noncomputable def ptAt (T i : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul (nat_lit 16) i)) (nat_lit 65535)

@[expose] noncomputable def lenL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def getL (l : List Nat) (k : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih k => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) k) l k

@[expose] noncomputable def frameOK (T : Nat) (fr : List Nat) : Bool :=
  (fun i0 i1 i2 i3 =>
    bAnd(Nat.beq (lenL fr) (nat_lit 4),
    bAnd(Nat.blt i0 (nat_lit 2240), bAnd(Nat.blt i1 (nat_lit 2240),
    bAnd(Nat.blt i2 (nat_lit 2240), bAnd(Nat.blt i3 (nat_lit 2240),
    (fun c0 c1 c2 c3 =>
      bAnd(adjK c0 c1, bAnd(adjK c0 c2, bAnd(adjK c0 c3,
      bAnd(adjK c1 c2, bAnd(adjK c1 c3, adjK c2 c3))))))
      (ptAt T i0) (ptAt T i1) (ptAt T i2) (ptAt T i3)))))))
    (getL fr (nat_lit 0)) (getL fr (nat_lit 1)) (getL fr (nat_lit 2)) (getL fr (nat_lit 3))

@[expose] noncomputable def frameK (L : List Nat) (F : List (Array Nat)) : Bool :=
  strictB (packL L) fun T =>
    List.rec (motive := fun _ => Bool) true (fun fr _ ih => bAnd(frameOK T fr.toList, ih)) F

@[expose] noncomputable def allP : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 2240)) (nat_lit 1)

@[expose] noncomputable def bitOf (L : List Nat) (b : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Nat.lor (Nat.land (Nat.shiftRight p b) (nat_lit 1)) (Nat.shiftLeft ih (nat_lit 1))) L

@[expose] noncomputable def cst (c : Nat) : Nat := Nat.mul c allP

@[expose] noncomputable def mlo (x0 x1 y : Nat) : Nat :=
  m0 x0 x1 (cst (Nat.land y (nat_lit 1))) (cst (Nat.shiftRight y (nat_lit 1)))

@[expose] noncomputable def mhi (x0 x1 y : Nat) : Nat :=
  m1 x0 x1 (cst (Nat.land y (nat_lit 1))) (cst (Nat.shiftRight y (nat_lit 1)))

@[expose] noncomputable def hermP (X : Nat → Nat) (b e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Nat.xor acc
      (Bool.rec (motive := fun _ => Nat → Nat → Nat → Nat) mlo mhi (Nat.beq e (nat_lit 1))
        (X (Nat.mul (nat_lit 2) c)) (X (Nat.succ (Nat.mul (nat_lit 2) c))) (frobK (cdK b c))))
    (nat_lit 8)

@[expose] noncomputable def maskOf (X : Nat → Nat) (b0 b1 b2 b3 : Nat) : Nat :=
  strictN (hermP X b0 (nat_lit 0)) fun a0 => strictN (hermP X b0 (nat_lit 1)) fun a1 =>
  strictN (hermP X b1 (nat_lit 0)) fun a2 => strictN (hermP X b1 (nat_lit 1)) fun a3 =>
  strictN (hermP X b2 (nat_lit 0)) fun a4 => strictN (hermP X b2 (nat_lit 1)) fun a5 =>
  strictN (hermP X b3 (nat_lit 0)) fun a6 => strictN (hermP X b3 (nat_lit 1)) fun a7 =>
  Nat.xor allP (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Nat.lor acc (Nat.lor
      (Nat.xor (X (Nat.mul (nat_lit 2) c))
        (Nat.xor (Nat.xor (mlo a0 a1 (cdK b0 c)) (mlo a2 a3 (cdK b1 c)))
          (Nat.xor (mlo a4 a5 (cdK b2 c)) (mlo a6 a7 (cdK b3 c)))))
      (Nat.xor (X (Nat.succ (Nat.mul (nat_lit 2) c)))
        (Nat.xor (Nat.xor (mhi a0 a1 (cdK b0 c)) (mhi a2 a3 (cdK b1 c)))
          (Nat.xor (mhi a4 a5 (cdK b2 c)) (mhi a6 a7 (cdK b3 c)))))))
    (nat_lit 8))

@[expose] noncomputable def frMask (X : Nat → Nat) (T : Nat) (fr : List Nat) : Nat :=
  maskOf X (ptAt T (getL fr (nat_lit 0))) (ptAt T (getL fr (nat_lit 1)))
    (ptAt T (getL fr (nat_lit 2))) (ptAt T (getL fr (nat_lit 3)))

@[expose] noncomputable def masksN (X : Nat → Nat) (T : Nat) (M : Nat → Nat) (n : Nat) :
    Nat → List (Array Nat) → Bool :=
  Nat.rec (motive := fun _ => Nat → List (Array Nat) → Bool) (fun _ _ => true)
    (fun _ ih j F => List.rec (motive := fun _ => Bool) false
      (fun fr F' _ => bAnd(Nat.beq (frMask X T fr.toList) (M j), ih (Nat.succ j) F')) F) n

@[expose] noncomputable def dropL {α : Type} (k : Nat) (l : List α) : List α :=
  Nat.rec (motive := fun _ => List α → List α) (fun l => l)
    (fun _ ih l => ih (List.rec (motive := fun _ => List α) [] (fun _ t _ => t) l)) k l

@[expose] noncomputable def masksK (L : List Nat) (F : List (Array Nat)) (M : Nat → Nat)
    (k n : Nat) : Bool :=
  strictB (packL L) fun T => masksN (bitOf L) T M n k (dropL k F)

@[expose] noncomputable def mulP (e x0 x1 y : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (mlo x0 x1 y) (mhi x0 x1 y) (Nat.beq e (nat_lit 1))

@[expose] noncomputable def polarP (X : Nat → Nat) (u e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Nat.xor acc (Nat.xor
      (mulP e (X (Nat.mul (nat_lit 2) (Nat.add c (nat_lit 4))))
        (X (Nat.succ (Nat.mul (nat_lit 2) (Nat.add c (nat_lit 4))))) (cdK u c))
      (mulP e (X (Nat.mul (nat_lit 2) c)) (X (Nat.succ (Nat.mul (nat_lit 2) c)))
        (cdK u (Nat.add c (nat_lit 4))))))
    (nat_lit 4)

@[expose] noncomputable def hermQ (X : Nat → Nat) (u e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.xor acc
      (mulP e (Nat.xor (X (Nat.mul (nat_lit 2) k)) (X (Nat.succ (Nat.mul (nat_lit 2) k))))
        (X (Nat.succ (Nat.mul (nat_lit 2) k))) (cdK u k)))
    (nat_lit 8)

@[expose] noncomputable def adjRow (X : Nat → Nat) (u i : Nat) : Nat :=
  Nat.xor (Nat.lor (Nat.shiftLeft (nat_lit 1) i)
      (Nat.lor (Nat.lor (polarP X u (nat_lit 0)) (polarP X u (nat_lit 1)))
        (Nat.lor (hermQ X u (nat_lit 0)) (hermQ X u (nat_lit 1)))))
    allP

@[expose] noncomputable def rowsK (L : List Nat) (A : Nat → Nat) (k n : Nat) : Bool :=
  strictB (packL L) fun T =>
    allBlk k (fun i => Nat.beq (adjRow (bitOf L) (ptAt T i) i) (A i)) n

@[expose] noncomputable def abv (x p : Nat) : Nat :=
  Nat.shiftLeft (Nat.shiftRight x (Nat.succ p)) (Nat.succ p)

@[expose] noncomputable def bitAt (x i : Nat) : Bool :=
  Nat.blt (nat_lit 0) (Nat.land x (Nat.shiftLeft (nat_lit 1) i))

@[expose] noncomputable def plOfF {β : Type} (l : List (Nat × β)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t _ ih => Nat.lor (Prod.rec (motive := fun _ => Nat) (fun r _ => Nat.shiftLeft (nat_lit 1) r) t) ih) l

@[expose] noncomputable def triOK (R M : Nat → Nat) (p q C : Nat) (t : Nat × List Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun r js =>
    strictB (abv (Nat.land C (R r)) r) fun D =>
    List.rec (motive := fun _ => Nat → Bool) (fun u => Nat.beq (Nat.land D u) D)
      (fun j _ ih u => bAnd(Nat.blt j (nat_lit 4480), strictB (M j) fun m =>
        bAnd(bitAt m p, bAnd(bitAt m q, bAnd(bitAt m r, ih (Nat.lor u m)))))) js (nat_lit 0)) t

@[expose] noncomputable def pairOK (R M : Nat → Nat) (p Rp : Nat)
    (e : Nat × List (Nat × List Nat)) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun q rs =>
    strictB (abv (Nat.land Rp (R q)) q) fun C =>
    bAnd(Nat.beq (plOfF rs) C,
      List.rec (motive := fun _ => Bool) true (fun t _ ih => bAnd(triOK R M p q C t, ih)) rs)) e

@[expose] noncomputable def ptOK (R M : Nat → Nat) (p : Nat)
    (E : List (Nat × List (Nat × List Nat))) : Bool :=
  strictB (R p) fun Rp => bAnd(Nat.beq (plOfF E) (abv Rp p),
    List.rec (motive := fun _ => Bool) true (fun e _ ih => bAnd(pairOK R M p Rp e, ih)) E)

@[expose] noncomputable def cliqueN (R M : Nat → Nat) (n : Nat) :
    Nat → List (List (Nat × List (Nat × List Nat))) → Bool :=
  Nat.rec (motive := fun _ => Nat → List (List (Nat × List (Nat × List Nat))) → Bool)
    (fun _ _ => true)
    (fun _ ih p CL => List.rec (motive := fun _ => Bool) false
      (fun E CL' _ => bAnd(ptOK R M p E, ih (Nat.succ p) CL')) CL) n

@[expose] noncomputable def cliqueK (R M : Nat → Nat) (CL : List (List (Nat × List (Nat × List Nat))))
    (k n : Nat) : Bool :=
  cliqueN R M n k (dropL k CL)

@[expose] noncomputable def eachL (f : Nat → List Nat → Bool) (n : Nat) :
    Nat → List (List Nat) → Bool :=
  Nat.rec (motive := fun _ => Nat → List (List Nat) → Bool) (fun _ _ => true)
    (fun _ ih j LL => List.rec (motive := fun _ => Bool) false
      (fun l LL' _ => bAnd(f j l, ih (Nat.succ j) LL')) LL) n

@[expose] noncomputable def solA (M S : Nat → Nat) (j : Nat) (l : List Nat) : Bool :=
  bAnd(Nat.beq (plOf l) (M j),
    List.rec (motive := fun _ => Bool) true (fun i _ ih => bAnd(bitAt (S i) j, ih)) l)

@[expose] noncomputable def solB (M S : Nat → Nat) (i : Nat) (l : List Nat) : Bool :=
  bAnd(Nat.beq (plOf l) (S i),
    List.rec (motive := fun _ => Bool) true
      (fun j _ ih => bAnd(Nat.blt j (nat_lit 4480), bAnd(bitAt (M j) i, ih))) l)

@[expose] noncomputable def solAK (M S : Nat → Nat) (SP : List (List Nat)) (k n : Nat) : Bool :=
  eachL (solA M S) n k (dropL k SP)

@[expose] noncomputable def solBK (M S : Nat → Nat) (SI : List (List Nat)) (k n : Nat) : Bool :=
  eachL (solB M S) n k (dropL k SI)

@[expose] noncomputable def wJ (w : Nat) : Nat := Nat.land w (nat_lit 8191)

@[expose] noncomputable def wF (w o : Nat) : Nat := Nat.land (Nat.shiftRight w o) (nat_lit 4095)

@[expose] noncomputable def tfOf (TW : Nat → List Nat) (j : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun w _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) (wJ w)) ih) (TW j)

@[expose] noncomputable def twOK (R M : Nat → Nat) (j mj w : Nat) : Bool :=
  strictB (wJ w) fun j' => strictB (wF w (nat_lit 13)) fun p => strictB (wF w (nat_lit 25)) fun q =>
  strictB (wF w (nat_lit 37)) fun r =>
  bAnd(Nat.blt j' (nat_lit 4480), bAnd(Bool.rec (motive := fun _ => Bool) true false (Nat.beq j' j),
  bAnd(bitAt mj p, bAnd(bitAt mj q, bAnd(bitAt mj r, strictB (M j') fun mj' =>
  bAnd(bitAt mj' p, bAnd(bitAt mj' q, bAnd(bitAt mj' r, strictB (R p) fun rp =>
  bAnd(bitAt rp q, bAnd(bitAt rp r, bitAt (R q) r))))))))))

@[expose] noncomputable def triSK (R M : Nat → Nat) (TW : Nat → List Nat) (k n : Nat) : Bool :=
  allBlk k (fun j => strictB (M j) fun mj =>
    List.rec (motive := fun _ => Bool) true (fun w _ ih => bAnd(twOK R M j mj w, ih)) (TW j)) n

@[expose] noncomputable def tfK (TW : Nat → List Nat) (TF : Nat → Nat) (k n : Nat) : Bool :=
  allBlk k (fun j => Nat.beq (tfOf TW j) (TF j)) n

@[expose] noncomputable def tagT (f : Nat → Nat) (i : Nat) : Nat :=
  Nat.lor (Nat.shiftLeft (f i) (nat_lit 64)) (Nat.succ i)

@[expose] noncomputable def triCt (S TF : Nat → Nat) (Spq : Nat) (t : Nat × List Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun r js =>
    bAnd(Nat.beq (plOf js) (Nat.shiftRight (Nat.land Spq (S r)) (nat_lit 64)),
      List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(strictB (TF a) fun ta =>
        List.rec (motive := fun _ => Bool) true
          (fun b _ ih2 => bAnd(bIf(Nat.beq a b, true, bitAt ta (Nat.add b (nat_lit 64))), ih2)) js,
        ih)) js)) t

@[expose] noncomputable def triCp (S TF : Nat → Nat) (Sp : Nat)
    (e : Nat × List (Nat × List Nat)) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun q rs => strictB (Nat.land Sp (S q)) fun Spq =>
    List.rec (motive := fun _ => Bool) true (fun t _ ih => bAnd(triCt S TF Spq t, ih)) rs) e

@[expose] noncomputable def triCpt (S TF : Nat → Nat) (p : Nat)
    (E : List (Nat × List (Nat × List Nat))) : Bool :=
  strictB (S p) fun Sp =>
    List.rec (motive := fun _ => Bool) true (fun e _ ih => bAnd(triCp S TF Sp e, ih)) E

@[expose] noncomputable def eachCL (f : Nat → List (Nat × List (Nat × List Nat)) → Bool) (n : Nat) :
    Nat → List (List (Nat × List (Nat × List Nat))) → Bool :=
  Nat.rec (motive := fun _ => Nat → List (List (Nat × List (Nat × List Nat))) → Bool)
    (fun _ _ => true)
    (fun _ ih p CL => List.rec (motive := fun _ => Bool) false
      (fun E CL' _ => bAnd(f p E, ih (Nat.succ p) CL')) CL) n

@[expose] noncomputable def triCK (S TF : Nat → Nat)
    (CL : List (List (Nat × List (Nat × List Nat)))) (k n : Nat) : Bool :=
  eachCL (triCpt (tagT S) (tagT TF)) n k (dropL k CL)

@[expose] noncomputable def allS : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 4480)) (nat_lit 1)

@[expose] noncomputable def cstS (c : Nat) : Nat := Nat.mul c allS

@[expose] noncomputable def fpOf (T : Nat) (F : List (Array Nat)) (s b : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun fr _ ih => Nat.lor (Nat.land (Nat.shiftRight (ptAt T (getL fr.toList s)) b) (nat_lit 1))
      (Nat.shiftLeft ih (nat_lit 1))) F

@[expose] noncomputable def fpK (L : List Nat) (F : List (Array Nat)) (FP : Nat → Nat) : Bool :=
  strictB (packL L) fun T => allBlk (nat_lit 0) (fun t =>
    Nat.beq (fpOf T F (Nat.shiftRight t (nat_lit 4)) (Nat.land t (nat_lit 15))) (FP t)) (nat_lit 64)

@[expose] noncomputable def mulS (e x0 x1 y : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (m0 x0 x1 (cstS (Nat.land y (nat_lit 1))) (cstS (Nat.shiftRight y (nat_lit 1))))
    (m1 x0 x1 (cstS (Nat.land y (nat_lit 1))) (cstS (Nat.shiftRight y (nat_lit 1))))
    (Nat.beq e (nat_lit 1))

@[expose] noncomputable def hermS (FP : Nat → Nat) (x s e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => (fun lo hi => Nat.xor acc (mulS e (Nat.xor lo hi) hi (cdK x c)))
      (FP (Nat.add (Nat.mul (nat_lit 16) s) (Nat.mul (nat_lit 2) c)))
      (FP (Nat.succ (Nat.add (Nat.mul (nat_lit 16) s) (Nat.mul (nat_lit 2) c)))))
    (nat_lit 8)

@[expose] noncomputable def fpc (FP : Nat → Nat) (s c e : Nat) : Nat :=
  FP (Nat.add (Nat.add (Nat.mul (nat_lit 16) s) (Nat.mul (nat_lit 2) c)) e)

@[expose] noncomputable def cxOf (FP : Nat → Nat) (x : Nat) : Nat :=
  strictN (hermS FP x (nat_lit 0) (nat_lit 0)) fun a0 => strictN (hermS FP x (nat_lit 0) (nat_lit 1)) fun a1 =>
  strictN (hermS FP x (nat_lit 1) (nat_lit 0)) fun a2 => strictN (hermS FP x (nat_lit 1) (nat_lit 1)) fun a3 =>
  strictN (hermS FP x (nat_lit 2) (nat_lit 0)) fun a4 => strictN (hermS FP x (nat_lit 2) (nat_lit 1)) fun a5 =>
  strictN (hermS FP x (nat_lit 3) (nat_lit 0)) fun a6 => strictN (hermS FP x (nat_lit 3) (nat_lit 1)) fun a7 =>
  Nat.xor allS (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Nat.lor acc (Nat.lor
      (Nat.xor (cstS (Nat.land (cdK x c) (nat_lit 1)))
        (Nat.xor
          (Nat.xor (m0 a0 a1 (fpc FP (nat_lit 0) c (nat_lit 0)) (fpc FP (nat_lit 0) c (nat_lit 1))) (m0 a2 a3 (fpc FP (nat_lit 1) c (nat_lit 0)) (fpc FP (nat_lit 1) c (nat_lit 1))))
          (Nat.xor (m0 a4 a5 (fpc FP (nat_lit 2) c (nat_lit 0)) (fpc FP (nat_lit 2) c (nat_lit 1))) (m0 a6 a7 (fpc FP (nat_lit 3) c (nat_lit 0)) (fpc FP (nat_lit 3) c (nat_lit 1))))))
      (Nat.xor (cstS (Nat.shiftRight (cdK x c) (nat_lit 1)))
        (Nat.xor
          (Nat.xor (m1 a0 a1 (fpc FP (nat_lit 0) c (nat_lit 0)) (fpc FP (nat_lit 0) c (nat_lit 1))) (m1 a2 a3 (fpc FP (nat_lit 1) c (nat_lit 0)) (fpc FP (nat_lit 1) c (nat_lit 1))))
          (Nat.xor (m1 a4 a5 (fpc FP (nat_lit 2) c (nat_lit 0)) (fpc FP (nat_lit 2) c (nat_lit 1))) (m1 a6 a7 (fpc FP (nat_lit 3) c (nat_lit 0)) (fpc FP (nat_lit 3) c (nat_lit 1))))))))
    (nat_lit 8))

@[expose] noncomputable def cxK (FP XC CX : Nat → Nat) (k n : Nat) : Bool :=
  allBlk k (fun t => Nat.beq (cxOf FP (XC t)) (CX t)) n

@[expose] noncomputable def smulK (a v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Nat.lor acc (Nat.shiftLeft (mulK a (cdK v c)) (Nat.mul (nat_lit 2) c))) (nat_lit 8)

@[expose] noncomputable def vecOK (XC : Nat → Nat) (nx u v c f : Nat) : Bool :=
  strictB (Nat.land f (nat_lit 8191)) fun k => strictB (Nat.shiftRight f (nat_lit 13)) fun l =>
  bAnd(Nat.blt k nx, bAnd(Nat.blt (nat_lit 0) l,
    Nat.beq (smulK l (Nat.xor u (smulK c v))) (XC k)))

@[expose] noncomputable def apW (XC : Nat → Nat) (nx T mj w : Nat) : Bool :=
  strictB (Nat.land w (nat_lit 4095)) fun a => strictB (wF w (nat_lit 12)) fun b =>
  strictB (ptAt T a) fun u => strictB (ptAt T b) fun v =>
  bAnd(bitAt mj a, bAnd(bitAt mj b,
  bAnd(vecOK XC nx u v (nat_lit 1) (Nat.land (Nat.shiftRight w (nat_lit 24)) (nat_lit 32767)),
  bAnd(vecOK XC nx u v (nat_lit 2) (Nat.land (Nat.shiftRight w (nat_lit 39)) (nat_lit 32767)),
    vecOK XC nx u v (nat_lit 3) (Nat.land (Nat.shiftRight w (nat_lit 54)) (nat_lit 32767))))))

@[expose] noncomputable def apC (SF CX : Nat → Nat) (w : Nat) : Nat :=
  Nat.xor allS (Nat.lor (Nat.lor (SF (Nat.land w (nat_lit 4095))) (SF (wF w (nat_lit 12))))
    (Nat.lor (CX (Nat.land (Nat.shiftRight w (nat_lit 24)) (nat_lit 8191)))
      (Nat.lor (CX (Nat.land (Nat.shiftRight w (nat_lit 39)) (nat_lit 8191)))
        (CX (Nat.land (Nat.shiftRight w (nat_lit 54)) (nat_lit 8191))))))

@[expose] noncomputable def apOK (M SF TF XC CX : Nat → Nat) (AP : Nat → List Nat) (nx T j : Nat) :
    Bool :=
  strictB (M j) fun mj =>
  bAnd(List.rec (motive := fun _ => Bool) true (fun w _ ih => bAnd(apW XC nx T mj w, ih)) (AP j),
    Nat.beq (Nat.lor (TF j) (Nat.lor (Nat.shiftLeft (nat_lit 1) j)
      (List.rec (motive := fun _ => Nat) (nat_lit 0) (fun w _ ih => Nat.lor (apC SF CX w) ih) (AP j))))
      allS)

@[expose] noncomputable def apK (L : List Nat) (M SF TF XC CX : Nat → Nat) (AP : Nat → List Nat)
    (nx k n : Nat) : Bool :=
  strictB (packL L) fun T => allBlk k (apOK M SF TF XC CX AP nx T) n

@[expose] noncomputable def incK (M : Nat → Nat) (n : Nat) : Bool :=
  allN n (fun j => Nat.blt (M j) (M (Nat.succ j)))

end CFSG.KC.D4Q2K

end
