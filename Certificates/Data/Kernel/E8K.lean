module

public import Certificates.Data.Kernel.Misc.PermM22

public section

namespace CFSG.KC.E8K

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.Misc.M22

@[expose] noncomputable def bit (m i : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight m i) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def fd (r i : Nat) : Nat :=
  Nat.land (Nat.shiftRight r (Nat.mul (nat_lit 8) i)) (nat_lit 255)

@[expose] noncomputable def eqB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB b) b a

@[expose] noncomputable def inI (MK : Nat → Nat) (k : Nat) : Bool := bit (MK k) k

@[expose] noncomputable def maskL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ acc => Nat.lor (Nat.shiftLeft (nat_lit 1) x) acc) L

@[expose] noncomputable def nodupL (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x t ih => andB (notB (anyL t fun y => Nat.beq y x)) ih) L

@[expose] noncomputable def spanL (a b c ab ac bc abc : Nat) : List Nat :=
  [nat_lit 0, a, b, c, ab, ac, bc, abc]

@[expose] noncomputable def invAt (n : Nat) (E MK : Nat → Nat) (k : Nat) : Bool :=
  eqB (inI MK k) (andB (Nat.blt (nat_lit 0) k) (Nat.beq (mul n (E k) (E k)) (one n)))

@[expose] noncomputable def cellAt (n N : Nat) (E MK R : Nat → Nat) (a b : Nat) : Bool :=
  letB (fd (R a) b) fun t =>
    andB (eqB (bit (MK a) b) (andB (inI MK b) (notB (Nat.beq t (nat_lit 255)))))
      (impB (inI MK b) (Bool.rec (motive := fun _ => Bool) (notB (comm n (E a) (E b)))
        (andB (Nat.blt t N) (andB (Nat.beq (E t) (mul n (E a) (E b))) (comm n (E a) (E b))))
        (notB (Nat.beq t (nat_lit 255)))))

@[expose] noncomputable def pairAt (n N : Nat) (E MK R : Nat → Nat) (a : Nat) : Bool :=
  impB (inI MK a) (allN N fun b => cellAt n N E MK R a b)

abbrev Head := Nat × Nat × Nat × Nat × Nat
abbrev PL := List (Nat × List Nat)
abbrev Wit := Head × (PL × List (List Nat)) × (PL × List (List Nat)) × (PL × List Nat)

@[expose] noncomputable def Wit.mask (w : Wit) : Nat := w.1.2.2.2.2

@[expose] noncomputable def anyW (W : List Wit) (f : Wit → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun w _ ih => orB (f w) ih) W

@[expose] noncomputable def allW (W : List Wit) (f : Wit → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun w _ ih => andB (f w) ih) W

@[expose] noncomputable def allP (L : PL) (f : Nat → List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun p _ ih => andB (f p.1 p.2) ih) L

@[expose] noncomputable def anyP (L : PL) (f : Nat → List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun p _ ih => orB (f p.1 p.2) ih) L

@[expose] noncomputable def nthP (L : PL) (f : Nat → List Nat → Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun p _ ih j => Nat.rec (motive := fun _ => Nat) (f p.1 p.2) (fun j' _ => ih j') j) L i

@[expose] noncomputable def triAt (N : Nat) (MK R : Nat → Nat) (W : List Wit) (a : Nat) : Bool :=
  impB (inI MK a) (letB (MK a) fun ma => allN N fun b =>
    impB (andB (bit ma b) (notB (Nat.beq b a))) (letB (fd (R a) b) fun ab =>
      letB (Nat.land ma (MK b)) fun mab => allN N fun c =>
        impB (andB (bit mab c) (notB (orB (Nat.beq c a) (orB (Nat.beq c b) (Nat.beq c ab)))))
          (letB (Nat.land mab (MK c)) fun X =>
            letB (maskL (spanL a b c ab (fd (R a) c) (fd (R b) c) (fd (R ab) c))) fun S =>
              andB (Nat.beq (Nat.land X S) X) (anyW W fun w => Nat.beq (Wit.mask w) S))))

@[expose] noncomputable def oddW (nA s : Nat) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun l _ ih => Bool.rec (motive := fun _ => Bool) ih (notB ih)
      (orB (Nat.beq l s) (Nat.beq l (Nat.add s nA)))) w

@[expose] noncomputable def gensK (n : Nat) (A : Nat → Nat) (nA : Nat) (B : Nat → Nat) (k : Nat)
    (ws : List (List Nat)) : Bool :=
  allN nA fun j => andB (lettersK k (nthW ws j)) (Nat.beq (wordK n B k (nthW ws j)) (A j))

@[expose] noncomputable def witAt (n : Nat) (A : Nat → Nat) (nA s N : Nat) (E MK R : Nat → Nat)
    (w : Wit) : Bool :=
  let a := w.1.1
  let b := w.1.2.1
  let c := w.1.2.2.1
  let o := w.1.2.2.2.1
  let M := w.1.2.2.2.2
  let cent := w.2.1.1
  let cj := w.2.2.1.1
  let three := w.2.2.2.1
  let ow := w.2.2.2.2
  andB (andB (andB (Nat.blt a N) (andB (Nat.blt b N) (Nat.blt c N)))
    (andB (inI MK a) (andB (inI MK b) (inI MK c))))
  (andB (andB (bit (MK a) b) (andB (bit (MK a) c) (bit (MK b) c)))
  (andB (letB (fd (R a) b) fun ab =>
      andB (nodupL (spanL a b c ab (fd (R a) c) (fd (R b) c) (fd (R ab) c)))
        (Nat.beq M (maskL (spanL a b c ab (fd (R a) c) (fd (R b) c) (fd (R ab) c)))))
  (andB (allP cent fun x u => andB (bit M x) (andB (Nat.blt (nat_lit 0) x)
      (andB (lettersK nA u) (comm n (E x) (wordK n A nA u)))))
  (andB (gensK n A nA (nthP cent fun _ u => wordK n A nA u) cent.length w.2.1.2)
  (andB (allP cj fun x u => andB (bit M x) (lettersK nA u))
  (andB (gensK n A nA (nthP cj fun x u => conj n (wordK n A nA u) (E x)) cj.length
      w.2.2.1.2)
  (andB (allP three fun x u => andB (bit M x) (andB (lettersK nA u)
      (letB (wordK n A nA u) fun t => andB (notB (Nat.beq t (one n)))
        (andB (Nat.beq (mul n t (mul n t t)) (one n)) (comm n (E x) t)))))
  (andB (allN N fun k => impB (andB (bit M k) (Nat.blt (nat_lit 0) k))
      (anyP three fun x _ => Nat.beq x k))
  (andB (bit M o) (andB (lettersK nA ow)
    (andB (Nat.beq (wordK n A nA ow) (E o)) (oddW nA s ow))))))))))))

end CFSG.KC.E8K

end
