module

public import Certificates.Data.Kernel.Co2Cls

public section

namespace CFSG.KC.Co2JRank

open CFSG.KC.Loop CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2Cls

@[expose] noncomputable def walkJ (G : Nat → Nat) (pt : Nat → Nat → Bool) (k X v : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun X v => pt X v)
    (fun k ih X v => andK (ih X v)
      (letB (mulV X (G k)) fun X' => ih X' (Nat.add v (Nat.shiftLeft (nat_lit 1) k)))) k X v

@[expose] noncomputable def M484 : Nat :=
  Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 484)) (nat_lit 1)

@[expose] noncomputable def crAt (CR : Nat → Nat) (v j : Nat) : Nat :=
  fld(CR (Nat.shiftRight v (nat_lit 3)),
    Nat.add (Nat.mul (Nat.land v (nat_lit 7)) (nat_lit 1936)) (Nat.mul (nat_lit 484) j), M484)

@[expose] noncomputable def kAt (T v : Nat) : Nat := fld(T, Nat.mul (nat_lit 4) v, nat_lit 15)

@[expose] noncomputable def pt1 (CR : Nat → Nat) (K1 X v : Nat) : Bool :=
  rankL (Nat.xor X IDP) (crAt CR v 0) (crAt CR v 1) (kAt K1 v)

@[expose] noncomputable def ptJ (CR : Nat → Nat) (K1 K3 R vr X v : Nat) : Bool :=
  andK (pt1 CR K1 X v)
    (implK (andK (Nat.beq (kAt K1 v) (nat_lit 10)) (Nat.beq (kAt K1 (Nat.xor v vr)) (nat_lit 10)))
      (rankL (mulV (Nat.xor R IDP) (Nat.xor X IDP)) (crAt CR v 2) (crAt CR v 3) (kAt K3 v)))

@[expose] noncomputable def clsOf (a b c : Nat) : Nat :=
  selN (Nat.beq a (nat_lit 6))
    (selN (Nat.beq b (nat_lit 0)) (nat_lit 0) (selN (Nat.beq b (nat_lit 8)) (nat_lit 2)
      (selN (Nat.beq b (nat_lit 10)) (nat_lit 7) (nat_lit 10))))
    (selN (Nat.beq a (nat_lit 8))
      (selN (Nat.beq b (nat_lit 8)) (nat_lit 1) (selN (Nat.beq b (nat_lit 6)) (nat_lit 3)
        (selN (Nat.beq b (nat_lit 10)) (nat_lit 5) (nat_lit 10))))
      (selN (Nat.beq a (nat_lit 10))
        (selN (Nat.beq b (nat_lit 10))
          (selN (Nat.beq c (nat_lit 2)) (nat_lit 4) (selN (Nat.beq c (nat_lit 3)) (nat_lit 9) (nat_lit 10)))
          (selN (Nat.beq b (nat_lit 8)) (nat_lit 6) (selN (Nat.beq b (nat_lit 6)) (nat_lit 8) (nat_lit 10))))
        (nat_lit 10)))

@[expose] noncomputable def clsJ (K1 K3 vr v : Nat) : Nat :=
  clsOf (kAt K1 v) (kAt K1 (Nat.xor v vr)) (kAt K3 v)

@[expose] noncomputable def tbK (m i : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight m i) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def oneIf (b : Bool) : Nat := selN b (nat_lit 1) (nat_lit 0)

@[expose] noncomputable def eqB (a b : Bool) : Bool := bIf(a, b, notK b)

@[expose] noncomputable def orK (a b : Bool) : Bool := bIf(a, true, b)

@[expose] noncomputable def fldJ (W i : Nat) : Nat :=
  fld(W, Nat.mul (nat_lit 10) i, nat_lit 1023)

@[expose] noncomputable def xorF (W n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i acc => Nat.xor acc (fldJ W i)) n

@[expose] noncomputable def allF (W n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => andK (p (fldJ W i)) acc) n

@[expose] noncomputable def xsub (C n u : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.xor acc (selN (tbK u i) (fldJ C i) (nat_lit 0))) n

@[expose] noncomputable def spanJ (C n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun u acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (xsub C n u)))
    (Nat.shiftLeft (nat_lit 1) n)

@[expose] noncomputable def popJ (S : Nat) : Nat :=
  sumBelow (nat_lit 1024) (nat_lit 16) fun v => oneIf (tbK S v)

@[expose] noncomputable def nzK (K1 N hi : Nat) : Bool :=
  allBelow N hi fun v => implK (Nat.blt (nat_lit 0) v) (Nat.blt (nat_lit 0) (kAt K1 v))

@[expose] noncomputable def cntJ (K1 K3 vr c : Nat) : Nat :=
  sumBelow (nat_lit 1024) (nat_lit 16) fun v => oneIf (Nat.beq (clsJ K1 K3 vr v) c)

@[expose] noncomputable def cntK (K1 K3 vr CNT : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun c acc => andK
    (Nat.beq (cntJ K1 K3 vr c) (fld(CNT, Nat.mul (nat_lit 12) c, nat_lit 4095))) acc) (nat_lit 10)

@[expose] noncomputable def omC (c : Nat) : Bool :=
  orK (Nat.beq c (nat_lit 0)) (orK (Nat.beq c (nat_lit 2)) (Nat.beq c (nat_lit 7)))

@[expose] noncomputable def omK (K1 K3 vr OM : Nat) : Bool :=
  andK (Nat.blt OM (Nat.shiftLeft (nat_lit 1) (nat_lit 1024)))
    (allBelow (nat_lit 1024) (nat_lit 16) fun v => eqB (tbK OM v) (omC (clsJ K1 K3 vr v)))

@[expose] noncomputable def olK (OM OL m : Nat) : Bool :=
  andK (Nat.beq (popJ OM) m)
    (Nat.rec (motive := fun _ => Bool) true (fun i acc => andK
      (andK (tbK OM (fldJ OL i))
        (implK (Nat.blt (Nat.succ i) m) (Nat.blt (fldJ OL i) (fldJ OL (Nat.succ i))))) acc) m)

@[expose] noncomputable def nJ (OM OL m y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (oneIf (tbK OM (Nat.xor (fldJ OL i) y)))) m

@[expose] noncomputable def nK (K1 K3 vr OM OL m NT : Nat) : Bool :=
  allBelow (nat_lit 1024) (nat_lit 16) fun y => letB (clsJ K1 K3 vr y) fun c =>
    implK (Nat.blt c (nat_lit 9))
      (Nat.beq (nJ OM OL m y) (fld(NT, Nat.mul (nat_lit 4) c, nat_lit 15)))

@[expose] noncomputable def w5K (OM W5 : Nat) : Bool :=
  andK (allF W5 (nat_lit 5) fun t => tbK OM t) (Nat.beq (xorF W5 (nat_lit 5)) (nat_lit 0))

@[expose] noncomputable def w3K (K1 K3 vr W3 : Nat) : Bool :=
  andK (allF W3 (nat_lit 3) fun t => Nat.beq (clsJ K1 K3 vr t) (nat_lit 4))
    (letB (xorF W3 (nat_lit 3)) fun s => orK (Nat.beq s (nat_lit 0)) (Nat.beq s vr))

@[expose] noncomputable def vC (c : Nat) : Bool :=
  orK (Nat.beq c (nat_lit 0)) (Nat.beq c (nat_lit 7))

@[expose] noncomputable def spK (K1 K3 vr C : Nat) : Bool :=
  letB (spanJ C (nat_lit 6)) fun S =>
    andK (Nat.beq (popJ S) (nat_lit 64))
      (andK (allBelow (nat_lit 1024) (nat_lit 16) fun v => implK (vC (clsJ K1 K3 vr v)) (tbK S v))
        (allF C (nat_lit 6) fun t => vC (clsJ K1 K3 vr t)))

@[expose] noncomputable def tabJ (K1 K3 vr CNT OM OL m NT W5 W3 C : Nat) : Bool :=
  andK (nzK K1 (nat_lit 1024) (nat_lit 16)) (andK (cntK K1 K3 vr CNT) (andK (omK K1 K3 vr OM)
    (andK (olK OM OL m) (andK (nK K1 K3 vr OM OL m NT) (andK (w5K OM W5)
      (andK (w3K K1 K3 vr W3) (spK K1 K3 vr C)))))))

@[expose] noncomputable def evenK (n v : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => bIf(tbK v i, notK acc, acc)) n

@[expose] noncomputable def parK (K1 n : Nat) : Bool :=
  allBelow (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1) fun v =>
    eqB (andK (notK (Nat.beq v (nat_lit 0))) (evenK n v))
      (andK (Nat.beq (kAt K1 v) (nat_lit 8)) (Nat.beq (kAt K1 (Nat.xor v (nat_lit 1))) (nat_lit 6)))

end CFSG.KC.Co2JRank

end
