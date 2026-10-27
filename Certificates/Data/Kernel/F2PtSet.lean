module

public import Certificates.Data.Kernel.F2TriSep

public section

namespace CFSG.KC.F2PtSet

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2

@[expose] noncomputable def hiOf (n : Nat) : Nat := Nat.succ (Nat.shiftRight n (nat_lit 6))

@[expose] noncomputable def sortK (d n P : Nat) : Bool :=
  allBelow (Nat.pred n) (hiOf n) fun i => Nat.blt (fget P i d) (fget P (Nat.succ i) d)

@[expose] noncomputable def gapK (d n P z j : Nat) : Bool :=
  andB (Nat.ble j n) (andB (orB (Nat.beq j (nat_lit 0)) (Nat.ble (fget P (Nat.pred j) d) z))
    (orB (Nat.beq j n) (Nat.blt z (fget P j d))))

@[expose] noncomputable def inW (d P z j : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) j) (Nat.beq (fget P (Nat.pred j) d) z)

@[expose] noncomputable def strictL (L : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun x _ ih k => strictB x fun x => ih fun L => k (x :: L)) L k

@[expose] noncomputable def imgK (d n P G T : Nat) : Bool :=
  strictB G fun G => allBelow n (hiOf n) fun i => strictB (fget T i (nat_lit 16)) fun k =>
    andB (Nat.blt k n) (Nat.beq (fget P k d) (vmF d G (fget P i d)))

@[expose] noncomputable def eqL (L M : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun M => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) M)
    (fun x _ ih M => List.rec (motive := fun _ => Bool) false
      (fun y M' _ => andB (Nat.beq x y) (ih M')) M) L M

@[expose] noncomputable def memK (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => orB (Nat.beq x y) ih) L

@[expose] noncomputable def depF (e : Nat) : Nat := Nat.shiftRight e (nat_lit 24)

@[expose] noncomputable def genF (e : Nat) : Nat := Nat.land (Nat.shiftRight e (nat_lit 16)) (nat_lit 255)

@[expose] noncomputable def parE (e : Nat) : Nat := Nat.land e (nat_lit 65535)

@[expose] noncomputable def forK (d n P E : Nat) (Gs roots : List Nat) : Bool :=
  strictL Gs fun Gs => strictL roots fun roots =>
  allBelow n (hiOf n) fun i => strictB (fget E i (nat_lit 32)) fun e =>
    strictB (fget P i d) fun x =>
      bIf(Nat.beq (depF e) (nat_lit 0), memK x roots,
        strictB (parE e) fun p => strictB (genF e) fun g =>
          andB (Nat.blt p n) (andB (Nat.blt g (lenL Gs))
            (andB (Nat.blt (depF (fget E p (nat_lit 32))) (depF e))
              (Nat.beq x (vmF d (getL (nat_lit 0) Gs g) (fget P p d))))))

@[expose] noncomputable def gapsK (d n P n' P' W : Nat) (h : Nat → Nat) : Bool :=
  allBelow n (hiOf n) fun i => gapK d n' P' (h (fget P i d)) (fget W i (nat_lit 16))

@[expose] noncomputable def eqB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB b) b a

@[expose] noncomputable def cntK (d n P P' W : Nat) (h : Nat → Nat) (f : Nat → Bool) (pos : Bool) :
    Nat :=
  sumBelow n (hiOf n) fun i => strictN (fget P i d) fun x =>
    nIf(andB (f x) (eqB (inW d P' (h x) (fget W i (nat_lit 16))) pos), nat_lit 1, nat_lit 0)

@[expose] noncomputable def hypF (m : Nat) : Nat :=
  orN m fun i => Nat.shiftLeft (pw2 (Nat.add m i)) (Nat.mul (Nat.add m m) i)

@[expose] noncomputable def ptsL (d P : Nat) (ix : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun k _ ih => fget P k d :: ih) ix

end CFSG.KC.F2PtSet

end
