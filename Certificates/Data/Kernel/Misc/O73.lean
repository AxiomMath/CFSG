module

public import Certificates.Data.Kernel.Misc.Base

public section

namespace CFSG.KC.Misc.O73

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

@[expose] noncomputable def ent (M a b : Nat) : Nat :=
  Nat.land (Nat.shiftRight M (Nat.mul 4 (Nat.add (Nat.mul 7 a) b))) 15

@[expose] noncomputable def ofFnM (f : Nat → Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun a acc => Nat.rec (motive := fun _ => Nat) acc
    (fun b acc2 => Nat.lor acc2 (Nat.shiftLeft (Nat.mod (f a b) 3)
      (Nat.mul 4 (Nat.add (Nat.mul 7 a) b)))) 7) 7

@[expose] noncomputable def mulM7 (A B : Nat) : Nat :=
  letN A fun A => letN B fun B => ofFnM fun a b =>
    Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Nat.add acc (Nat.mul (ent A a k) (ent B k b))) 7

@[expose] noncomputable def oneM7 : Nat := ofFnM fun a b => Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq a b)

@[expose] noncomputable def trM7 (A : Nat) : Nat := letN A fun A => ofFnM fun a b => ent A b a

@[expose] noncomputable def dig (x k : Nat) : Nat := Nat.mod (Nat.div x (Nat.pow 3 k)) 3

@[expose] noncomputable def appM7 (M x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun a acc => Nat.add acc (Nat.mul (Nat.pow 3 a)
    (Nat.mod (Nat.rec (motive := fun _ => Nat) 0
      (fun k acc2 => Nat.add acc2 (Nat.mul (ent M a k) (dig x k))) 7) 3))) 7

@[expose] noncomputable def crd (v : List Nat) (k : Nat) : Nat :=
  Nat.mod (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) v k) 3

@[expose] noncomputable def gvK (v : List Nat) (b : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (Nat.mul 2 (crd v 6)) (crd v (Nat.sub b 3)) (Nat.blt b 6))
    (crd v (Nat.add b 3)) (Nat.blt b 3)

@[expose] noncomputable def rK (v : List Nat) : Nat :=
  ofFnM fun a b => Nat.add (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq a b))
    (Nat.mul (crd v a) (gvK v b))

@[expose] noncomputable def tK (v : List Nat) : Nat :=
  letN (rK v) fun R => ofFnM fun a b => Nat.mul 2 (ent R a b)

@[expose] noncomputable def q3K (v : List Nat) : Nat :=
  Nat.mod (Nat.add (Nat.add (Nat.mul (crd v 0) (crd v 3)) (Nat.mul (crd v 1) (crd v 4)))
    (Nat.add (Nat.mul (crd v 2) (crd v 5)) (Nat.mul (crd v 6) (crd v 6)))) 3

@[expose] noncomputable def gramM : Nat :=
  ofFnM fun a b => Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) 0 1
      (orB (andB (Nat.blt a 3) (Nat.beq b (Nat.add a 3))) (andB (Nat.blt b 3) (Nat.beq a (Nat.add b 3)))))
    2 (andB (Nat.beq a 6) (Nat.beq b 6))

@[expose] noncomputable def wordM7 (Ms : List Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) oneM7 (fun c _ ih => mulM7
    (Bool.rec (motive := fun _ => Nat) oneM7 (nthN Ms c) (Nat.blt c (lenN Ms))) ih) w
where
  nthN (l : List Nat) (i : Nat) : Nat :=
    List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) l i

@[expose] noncomputable def at' (w P i : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul w i)) (Nat.sub (Nat.shiftLeft 1 w) 1)

@[expose] noncomputable def permK (n w P : Nat) : Bool :=
  letB P fun P => andB (Nat.blt P (Nat.shiftLeft 1 (Nat.mul w n)))
    (andB (allN n fun i => Nat.blt (at' w P i) n)
      (Nat.beq (Nat.rec (motive := fun _ => Nat) 0
        (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (at' w P i))) n) (Nat.sub (Nat.shiftLeft 1 n) 1)))

@[expose] noncomputable def compP (n w t u : Nat) : Nat :=
  letN t fun t => letN u fun u => Nat.rec (motive := fun _ => Nat) 0
    (fun x acc => Nat.lor acc (Nat.shiftLeft (at' w t (at' w u x)) (Nat.mul w x))) n

@[expose] noncomputable def idP (n w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun x acc => Nat.lor acc (Nat.shiftLeft x (Nat.mul w x))) n

@[expose] noncomputable def wordP (n w : Nat) (Ps : List Nat) (wd : List Nat) : Nat :=
  letN (idP n w) fun E => List.rec (motive := fun _ => Nat) E (fun c _ ih => compP n w
    (Bool.rec (motive := fun _ => Nat) E (wordM7.nthN Ps c) (Nat.blt c (lenN Ps))) ih) wd

@[expose] noncomputable def fmtK (cs : List Nat) : Bool :=
  allL cs fun c => orB (Nat.beq c 32) (orB (Nat.beq c 10) (andB (Nat.ble 48 c) (Nat.ble c 57)))

@[expose] noncomputable def tokLt (B : Nat) (cs : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun cur => Nat.ble cur B)
    (fun c _ ih cur => Bool.rec (motive := fun _ => Bool)
      (ih (Nat.succ (Nat.add (Nat.mul 10 (Nat.pred cur)) (Nat.sub c 48))))
      (andB (Nat.ble cur B) (ih 0)) (orB (Nat.beq c 32) (Nat.beq c 10))) cs 0

@[expose] noncomputable def parseK (w : Nat) (cs : List Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool → List Nat)
    (fun cur cnt acc ne => Bool.rec (motive := fun _ => List Nat) List.nil
      [fin w cur cnt acc] ne)
    (fun c _ ih cur cnt acc ne => Bool.rec (motive := fun _ => List Nat)
      (Bool.rec (motive := fun _ => List Nat)
        (ih (Nat.succ (Nat.add (Nat.mul 10 (Nat.pred cur)) (Nat.sub c 48))) cnt acc true)
        (Bool.rec (motive := fun _ => List Nat)
          (ih 0 (Nat.succ cnt) (Nat.lor acc (Nat.shiftLeft (Nat.pred cur) (Nat.mul w cnt))) true)
          (ih 0 cnt acc true) (Nat.beq cur 0))
        (Nat.beq c 32))
      (Bool.rec (motive := fun _ => List Nat) (ih 0 0 0 false)
        (List.cons (fin w cur cnt acc) (ih 0 0 0 false)) ne)
      (Nat.beq c 10)) cs 0 0 0 false
where
  fin (w cur cnt acc : Nat) : Nat :=
    Bool.rec (motive := fun _ => Nat)
      (Nat.add (Nat.succ cnt) (Nat.shiftLeft (Nat.lor acc (Nat.shiftLeft (Nat.pred cur)
        (Nat.mul w cnt))) 16))
      (Nat.add cnt (Nat.shiftLeft acc 16)) (Nat.beq cur 0)

@[expose] noncomputable def nthL (L : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) i) L i

@[expose] noncomputable def matK (VL : List (List Nat)) (Ts Rs : List Nat) : Bool :=
  andB (Nat.beq (lenN Ts) 8) <| andB (Nat.beq (lenN Rs) 8) <|
    allN 8 fun i => letB (wordM7.nthN Ts i) fun T => letB (wordM7.nthN Rs i) fun R =>
      andB (Nat.beq T (tK (nthL VL i))) <| andB (Nat.beq R (rK (nthL VL i))) <|
      andB (Nat.beq (q3K (nthL VL i)) 2) <| andB (Nat.beq (mulM7 T T) oneM7) <|
      andB (Nat.beq (mulM7 R R) oneM7) <| Nat.beq (mulM7 (trM7 T) (mulM7 gramM T)) gramM

@[expose] noncomputable def relMK (Ts Rs : List Nat) (R1 E : List (List Nat)) : Bool :=
  andB (allLL R1 fun w => andB (Nat.beq (wordM7 Ts w) oneM7) (Nat.beq (wordM7 Rs w) oneM7))
    (allLL E fun w => Nat.beq (wordM7 Ts w) oneM7)

@[expose] noncomputable def linesK (n m : Nat) (PL Ps : List Nat) : Bool :=
  andB (Nat.beq (lenN PL) m) (andB (Nat.beq (lenN Ps) m) (allN m fun i =>
    letB (wordM7.nthN PL i) fun l => andB (Nat.beq (Nat.land l 65535) n)
      (Nat.beq (Nat.shiftRight l 16) (wordM7.nthN Ps i))))

@[expose] noncomputable def liftTextK (cL : List Nat) (LP : List Nat) : Bool :=
  andB (fmtK cL) <| andB (tokLt 2048 cL) <| andB (linesK 1134 8 (parseK 11 cL) LP) <|
    allN 8 fun i => permK 1134 11 (wordM7.nthN LP i)

@[expose] noncomputable def relPK (LP : List Nat) (E : List (List Nat)) (lo n : Nat) : Bool :=
  allN n fun d => letB (Nat.add lo d) fun k => impB (Nat.blt k (lenLLN E))
    (Nat.beq (wordP 1134 11 LP (nthL E k)) (idP 1134 11))
where
  lenLLN (L : List (List Nat)) : Nat :=
    List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def spK (LP sp : List Nat) : Bool :=
  notB (Nat.beq (wordP 1134 11 LP sp) (idP 1134 11))

@[expose] noncomputable def betaK (Rs : List Nat) (cB cY : List Nat) (BP : Nat) (YP : List Nat) :
    Bool :=
  andB (fmtK cB) <| andB (tokLt 4096 cB) <| andB (linesK 728 1 (parseK 12 cB) [BP]) <|
  andB (fmtK cY) <| andB (tokLt 1024 cY) <| andB (linesK 728 8 (parseK 10 cY) YP) <|
  andB (allN 728 fun x => Nat.blt (at' 12 BP x) 2187) <|
  andB (Nat.beq (Nat.rec (motive := fun _ => Nat) 0
      (fun x acc => Nat.add acc (Nat.shiftLeft 1 (at' 12 BP x))) 728)
    (Nat.rec (motive := fun _ => Nat) 0
      (fun x acc => Nat.lor acc (Nat.shiftLeft 1 (at' 12 BP x))) 728)) <|
    allN 8 fun i => letB (wordM7.nthN Rs i) fun R => letB (wordM7.nthN YP i) fun Y =>
      allN 728 fun x => Nat.beq (appM7 R (at' 12 BP x)) (at' 12 BP (at' 10 Y x))

end CFSG.KC.Misc.O73

end
