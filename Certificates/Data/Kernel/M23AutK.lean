module

public import Certificates.Data.Kernel.LocalQT.Perm
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.M23Aut

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def fl (P w i : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul w i)) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def tC (n PT i : Nat) : Nat := fl PT (Nat.mul (nat_lit 5) n) i

@[expose] noncomputable def nth (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih k => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) k) l

@[expose] noncomputable def treeAt (n e N : Nat) (G : List Nat) (PT PP PG PD i : Nat) : Bool :=
  letB (tC n PT i) fun t =>
    andB (impB (Nat.blt (Nat.succ i) N) (Nat.blt t (tC n PT (Nat.succ i))))
      (letB (fl PD (nat_lit 8) i) fun d =>
        Bool.rec (motive := fun _ => Bool)
          (letB (fl PP (nat_lit 16) i) fun p =>
            andB (Nat.blt p N) (andB (Nat.beq (Nat.succ (fl PD (nat_lit 8) p)) d)
              (Nat.beq t (mul n (nth G (fl PG (nat_lit 4) i)) (tC n PT p)))))
          (Nat.beq t e)
          (Nat.beq d (nat_lit 0)))

@[expose] noncomputable def treeK (n e N : Nat) (G : List Nat) (PT PP PG PD : Nat) : Bool :=
  CFSG.KC.Enum.allN N (treeAt n e N G PT PP PG PD)

@[expose] noncomputable def ord8K (n e t : Nat) : Bool :=
  letB (mul n t t) fun t2 => letB (mul n t2 t2) fun t4 =>
    andB (notB (Nat.beq t4 e)) (Nat.beq (mul n t4 t4) e)

@[expose] noncomputable def ord2K (n e t : Nat) : Bool :=
  andB (notB (Nat.beq t e)) (Nat.beq (mul n t t) e)

@[expose] noncomputable def ord5K (n e t : Nat) : Bool :=
  andB (notB (Nat.beq t e)) (letB (mul n t t) fun t2 => Nat.beq (mul n (mul n t2 t2) t) e)

@[expose] noncomputable def ord3K (n e t : Nat) : Bool :=
  andB (notB (Nat.beq t e)) (Nat.beq (mul n (mul n t t) t) e)

@[expose] noncomputable def evAcc (n : Nat) (S w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => CFSG.KC.Enum.strictN (mul n acc (nth S l)) ih) w

@[expose] noncomputable def evK (n e : Nat) (S w : List Nat) : Nat := evAcc n S w e

@[expose] noncomputable def withInv (n : Nat) (S : List Nat) : List Nat :=
  S ++ List.map (inv n) S

@[expose] noncomputable def eqLK : List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false
      (fun y b' _ => andB (Nat.beq x y) (ih b')) b)

@[expose] noncomputable def setK (t : Nat) (B : List Nat) : Bool :=
  allL B fun p => anyL B fun q => Nat.beq (img t p) q

@[expose] noncomputable def fixK (t : Nat) (F : List Nat) : Bool :=
  allL F fun p => Nat.beq (img t p) p

@[expose] noncomputable def pairK (t a b : Nat) : Bool :=
  orB (andB (Nat.beq (img t a) a) (Nat.beq (img t b) b))
    (andB (Nat.beq (img t a) b) (Nat.beq (img t b) a))

@[expose] noncomputable def inPbarK (t : Nat) : Bool :=
  andB (fixK t [nat_lit 19, nat_lit 21, nat_lit 22])
    (setK t [nat_lit 5, nat_lit 7, nat_lit 9, nat_lit 16, nat_lit 19, nat_lit 21, nat_lit 22])

@[expose] noncomputable def inHbarK (t : Nat) : Bool :=
  andB (setK t [nat_lit 5, nat_lit 7, nat_lit 9, nat_lit 16, nat_lit 19, nat_lit 21, nat_lit 22])
    (pairK t (nat_lit 21) (nat_lit 22))

@[expose] noncomputable def inIxK (t : Nat) : Bool :=
  andB (pairK t (nat_lit 16) (nat_lit 19)) (pairK t (nat_lit 21) (nat_lit 22))

@[expose] noncomputable def inF4K (t : Nat) : Bool :=
  fixK t [nat_lit 16, nat_lit 19, nat_lit 21, nat_lit 22]

@[expose] noncomputable def cntN (N : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (f i))) N

@[expose] noncomputable def invAt (n e PT : Nat) (I2 : List Nat) (j : Nat) : Bool :=
  impB (ord2K n e (tC n PT j)) (anyL I2 (Nat.beq j))

@[expose] noncomputable def repIn (R : List (Nat × List (Nat × Nat))) (ri : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun r _ ih => orB (Nat.beq r.1 ri) ih) R

@[expose] noncomputable def orbAt (n e N pt PT PC PR : Nat) (R : List (Nat × List (Nat × Nat)))
    (i : Nat) : Bool :=
  letB (tC n PT i) fun x => impB (ord8K n e x)
    (letB (fl PC (nat_lit 16) i) fun ci => letB (fl PR (nat_lit 16) i) fun ri =>
      andB (Nat.blt ci N) (andB (repIn R ri)
        (letB (tC n PT ci) fun c => andB (Nat.beq (img c pt) pt)
          (Nat.beq (mul n c x) (mul n (tC n PT ri) c)))))

@[expose] noncomputable def pwK (n e : Nat) (S : List Nat) (pW : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => andB (inPbarK (evK n e S w)) ih) pW

@[expose] noncomputable def iwK (n e : Nat) (S : List Nat) (g : Nat) (iWT : List (List Nat × Nat)) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun wt _ ih => andB (Nat.beq (mul n (evK n e S wt.1) g) (mul n g wt.2)) ih) iWT

@[expose] noncomputable def anyW (W : List (Nat × Nat)) (j : Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun jg _ ih => orB (andB (Nat.beq jg.1 j) (f jg.2)) ih) W

@[expose] noncomputable def repK (n e N pt PT : Nat) (I2 : List Nat) (pW : List (List Nat))
    (iWT : List (List Nat × Nat)) (r : Nat × List (Nat × Nat)) : Bool :=
  andB (Nat.blt r.1 N) (letB (tC n PT r.1) fun x =>
    allL I2 fun j => letB (tC n PT j) fun y =>
      impB (andB (ord5K n e (mul n x y)) (pwK n e (withInv n [x, y]) pW))
        (anyW r.2 j fun gi => andB (Nat.blt gi N) (letB (tC n PT gi) fun g =>
          andB (Nat.beq (img g pt) pt) (iwK n e (withInv n [x, y]) g iWT))))

@[expose] noncomputable def scanK (n e N pt PT : Nat) (I2 : List Nat) (pW : List (List Nat))
    (iWT : List (List Nat × Nat)) (R : List (Nat × List (Nat × Nat))) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => andB (repK n e N pt PT I2 pW iWT r) ih) R

@[expose] noncomputable def sepK (n x f c d : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (notB (Nat.beq (mul n f x) (mul n x c)))
    (notB (Nat.beq (mul n x f) (mul n c x))) (Nat.beq d (nat_lit 0))

@[expose] noncomputable def autAt (n e PT lX : Nat) (FW : List (Nat × Nat × Nat)) (i : Nat) :
    Bool :=
  letB (tC n PT i) fun x => impB (andB (ord3K n e x) (notB (Nat.beq x lX)))
    (List.rec (motive := fun _ => Bool) false
      (fun r _ ih => orB (sepK n x (tC n PT r.1) (tC n PT r.2.1) r.2.2) ih) FW)

@[expose] noncomputable def fwOK (n N PT lX : Nat) (FW : List (Nat × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => andB (andB (Nat.blt r.1 N) (Nat.blt r.2.1 N))
      (letB (tC n PT r.1) fun f => letB (tC n PT r.2.1) fun c =>
        andB (andB (inF4K f) (inF4K c))
          (andB (Bool.rec (motive := fun _ => Bool) (Nat.beq (mul n lX c) (mul n f lX))
            (Nat.beq (mul n c lX) (mul n lX f)) (Nat.beq r.2.2 (nat_lit 0))) ih))) FW

end CFSG.KC.M23Aut

end
