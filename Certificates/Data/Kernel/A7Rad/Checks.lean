module

public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KC.A7Rad

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def fld (L k : Nat) : Nat := bitsN L (Nat.mul (nat_lit 35) k) (nat_lit 35)

@[expose] noncomputable def pk (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.add x (Nat.shiftLeft ih (nat_lit 35))) l

@[expose] noncomputable def memP (L n c : Nat) : Bool := anyN n fun k => Nat.beq (fld L k) c

@[expose] noncomputable def closedB (L n : Nat) : Bool :=
  andB (memP L n (one (nat_lit 7)))
    (andB (allN n fun i => allN n fun j => memP L n (mul (nat_lit 7) (fld L i) (fld L j)))
      (allN n fun i => memP L n (inv (nat_lit 7) (fld L i))))

@[expose] noncomputable def nodupB (L n : Nat) : Bool :=
  allN n fun i => allN i fun j => notB (Nat.beq (fld L i) (fld L j))

@[expose] noncomputable def pow4B (L n : Nat) : Bool :=
  allN n fun i => Nat.beq (pow (nat_lit 7) (fld L i) (nat_lit 4)) (one (nat_lit 7))

@[expose] noncomputable def subB (L n M m : Nat) : Bool := allN n fun i => memP M m (fld L i)

@[expose] noncomputable def nonabB (L n : Nat) : Bool :=
  anyN n fun i => anyN n fun j => notB (comm (nat_lit 7) (fld L i) (fld L j))

@[expose] noncomputable def conjB (T m P n : Nat) : Bool :=
  allN m fun t => allN n fun x => memP P n (conj (nat_lit 7) (fld T t) (fld P x))

@[expose] noncomputable def exB (T m P n : Nat) : Bool := anyN m fun t => notB (memP P n (fld T t))

@[expose] noncomputable def invU (P n z : Nat) : Bool :=
  andB (memP P n z) (andB (Nat.beq (mul (nat_lit 7) z z) (one (nat_lit 7)))
    (allN n fun k => letB (fld P k) fun x =>
      impB (andB (notB (Nat.beq x (one (nat_lit 7)))) (Nat.beq (mul (nat_lit 7) x x) (one (nat_lit 7))))
        (Nat.beq x z)))

@[expose] noncomputable def normB (P n T m z : Nat) : Bool :=
  andB (invU P n z) (allC (nat_lit 7) z fun g => impB (even (nat_lit 7) g)
    (impB (allN n fun k => memP P n (conj (nat_lit 7) g (fld P k)))
      (allN m fun k => memP T m (conj (nat_lit 7) g (fld T k)))))

@[expose] noncomputable def threeB (L n W : Nat) : Bool :=
  allN n fun i => letB (fld L i) fun x => impB (notB (Nat.beq x (one (nat_lit 7))))
    (allN n fun j => letB (bitsN W (Nat.mul (nat_lit 18) (Nat.add (Nat.mul n i) j)) (nat_lit 18))
      fun r => letB (bitsN r (nat_lit 0) (nat_lit 6)) fun a =>
        letB (bitsN r (nat_lit 6) (nat_lit 6)) fun b =>
          letB (bitsN r (nat_lit 12) (nat_lit 6)) fun c =>
            andB (Nat.blt a n) (andB (Nat.blt b n) (andB (Nat.blt c n)
              (Nat.beq (fld L j) (mul (nat_lit 7) (mul (nat_lit 7) (conj (nat_lit 7) (fld L a) x)
                (conj (nat_lit 7) (fld L b) x)) (conj (nat_lit 7) (fld L c) x))))))

@[expose] noncomputable def validB (L n : Nat) : Bool :=
  andB (nodupB L n) (allN n fun k => andB (permK (nat_lit 7) (fld L k)) (even (nat_lit 7) (fld L k)))

@[expose] noncomputable def bitB (m k : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight m k) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def closedM (D d m : Nat) : Bool :=
  andB (anyN d fun k => andB (bitB m k) (Nat.beq (fld D k) (one (nat_lit 7))))
    (andB (allN d fun i => impB (bitB m i) (allN d fun j => impB (bitB m j)
      (anyN d fun k => andB (bitB m k) (Nat.beq (fld D k) (mul (nat_lit 7) (fld D i) (fld D j))))))
      (allN d fun i => impB (bitB m i)
        (anyN d fun k => andB (bitB m k) (Nat.beq (fld D k) (inv (nat_lit 7) (fld D i))))))

@[expose] noncomputable def mkM (b : Nat → Bool) (K : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Nat.shiftLeft (nat_lit 1) k) (b k))) K

@[expose] noncomputable def maskOf (D d G nG : Nat) : Nat := mkM (fun k => memP G nG (fld D k)) d

@[expose] noncomputable def latB (D d : Nat) (ms : List Nat) : Bool :=
  allN (Nat.shiftLeft (nat_lit 1) d) fun m => impB (closedM D d m) (anyL ms (Nat.beq m))

end CFSG.KC.A7Rad

end
