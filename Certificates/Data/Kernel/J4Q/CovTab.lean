module

public import Certificates.Data.Kernel.J4Q.Mat
public import Certificates.Data.Kernel.SlpPc

public section

namespace CFSG.KC.J4Q.CovTab

open CFSG.KC.Loop CFSG.KC.J4Q CFSG.KC.SlpPc

@[expose] noncomputable def memN (x : Nat) (T : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => orB (Nat.beq x y) ih) T

@[expose] noncomputable def distN (T : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y ys ih => andB (notB (memN y ys)) ih) T

@[expose] noncomputable def entry (c rm one : Nat) (P1 P2 Z : List Nat) (i : Nat) : Nat :=
  strictN (mulJ c rm (nthD one P1 (Nat.div i 9)) (nthD one P2 (Nat.mod (Nat.div i 3) 3))) fun u =>
    mulJ c rm u (nthD one Z (Nat.mod i 3))

@[expose] noncomputable def tabFrom (c rm one : Nat) (P1 P2 Z : List Nat) (n : Nat) :
    List Nat → (List Nat → Bool) → Bool :=
  Nat.rec (motive := fun _ => List Nat → (List Nat → Bool) → Bool) (fun acc k => k acc)
    (fun i ih acc k => strictB (entry c rm one P1 P2 Z i) fun x => ih (List.cons x acc) k) n

@[expose] noncomputable def closOK (c rm g : Nat) (T : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih => andB (strictB (mulJ c rm x g) fun y => memN y T) ih) T

@[expose] noncomputable def cjOK (c rm one p1 : Nat) (R' : Nat → Nat) (T : List Nat)
    (cj : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => andB (andB (Nat.blt (nthD 0 e 0) 27)
      ((fun C => Nat.beq (mulJ c rm C (nthD one T (nthD 0 e 0))) (mulJ c rm p1 C))
        (R' (nthD 0 e 1)))) ih) cj

@[expose] noncomputable def cwOne (c rm one : Nat) (T : List Nat) (cj : List (List Nat))
    (X : Nat) (w : List Nat) : Bool :=
  (fun u j s => andB (Nat.blt u 27) (andB (Nat.blt j cj.length) (andB (Nat.blt s 2)
    ((fun U E => Bool.rec (motive := fun _ => Bool)
        (Nat.beq (mulJ c rm U X) (mulJ c rm E U))
        (Nat.beq (mulJ c rm (mulJ c rm E U) X) U) (Nat.beq s 1))
      (nthD one T u) (nthD one T (nthD 0 (nthD List.nil cj j) 0))))))
  (nthD 0 w 0) (nthD 0 w 1) (nthD 0 w 2)

@[expose] noncomputable def cwOK (c rm one : Nat) (T : List Nat) (cj : List (List Nat))
    (cw : List (List Nat)) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB (cwOne c rm one T cj (nthD one T (Nat.succ i)) (nthD List.nil cw (Nat.succ i)))
      ih) n

@[expose] noncomputable def fuOne (c rm one p1 g : Nat) (T : List Nat) (e : Nat) : Bool :=
  andB (Nat.blt e 27) (Nat.beq (mulJ c rm p1 g) (mulJ c rm g (nthD one T e)))

@[expose] noncomputable def xOK (one : Nat) (mats xr : List Nat) (bl : List (List Nat))
    (cur : List Nat) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k ih => andB (Nat.beq (lk one bl cur n (nthD 0 xr k)) (getN one mats k)) ih) 3

@[expose] noncomputable def tabOK (c rm one r p1 p2 g1 g2 g1i g2i t : Nat) (mats : List Nat)
    (R' : Nat → Nat) (T : List Nat) (cj cw : List (List Nat)) (fu : List Nat)
    (prg2 : List (Nat × Nat)) (xr : List Nat) : Bool :=
  andB (Nat.beq T.length 27) (andB (distN T) (andB (closOK c rm p1 T) (andB (closOK c rm p2 T)
  (andB (Nat.beq (nthD 0 (nthD List.nil cj 0) 0) 18)
  (andB (cjOK c rm one p1 R' T cj) (andB (cwOK c rm one T cj cw 26)
  (andB (fuOne c rm one p1 g1 T (nthD 0 fu 0)) (andB (fuOne c rm one p1 g2 T (nthD 0 fu 1))
  (andB (fuOne c rm one p1 t T (nthD 0 fu 2)) (andB (neN (vecJ rm r t) r)
  (andB (Nat.beq (mulJ c rm g1 g1i) one) (andB (Nat.beq (mulJ c rm g2 g2i) one)
    (runP (mulJ c rm) one prg2 List.nil [g2i, g1i, g2, g1, one] 5 fun bl cur n =>
      xOK one mats xr bl cur n)))))))))))))

@[expose] noncomputable def postOK (c rm one r : Nat) (mats : List Nat) (R R' : Nat → Nat)
    (cj cw : List (List Nat)) (fu : List Nat) (prg2 : List (Nat × Nat)) (xr : List Nat) : Bool :=
  strictB (R 0) fun p1 => strictB (R 1) fun p2 =>
  strictB (mulJ c rm p1 p1) fun s1 => strictB (mulJ c rm p2 p2) fun s2 =>
  strictB (mulJ c rm (mulJ c rm (mulJ c rm p1 p2) s1) s2) fun z =>
  strictB (mulJ c rm z z) fun s3 =>
  andB (Nat.beq (mulJ c rm s1 p1) one)
    (tabFrom c rm one [one, p1, s1] [one, p2, s2] [one, z, s3] 27 List.nil fun T =>
      strictB (R 2) fun g1 => strictB (R 3) fun g2 => strictB (R 4) fun g1i =>
      strictB (R 5) fun g2i => strictB (R 6) fun t =>
        tabOK c rm one r p1 p2 g1 g2 g1i g2i t mats R' T cj cw fu prg2 xr)

@[expose] noncomputable def chk (c rm one r : Nat) (mats invs : List Nat) (prg : List (Nat × Nat))
    (rp : List Nat) (cj cw : List (List Nat)) (fu : List Nat) (prg2 : List (Nat × Nat))
    (xr : List Nat) : Bool :=
  runP (mulJ c rm) one prg List.nil
    [getN one invs 4, getN one invs 3, getN one invs 2, getN one invs 1, getN one invs 0,
      getN one mats 4, getN one mats 3, getN one mats 2, getN one mats 1, getN one mats 0, one] 11
    fun bl cur n => postOK c rm one r mats (fun i => lk one bl cur n (nthD 0 rp i)) (lk one bl cur n)
      cj cw fu prg2 xr

end CFSG.KC.J4Q.CovTab

end
