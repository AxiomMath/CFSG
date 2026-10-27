module

public import Certificates.Data.Kernel.HNF26729K

public section

namespace CFSG.KC.HNFFib

open CFSG.KC.Ord CFSG.KC.HNF26720 CFSG.KC.HNF26729

@[expose] def decW (w : List Nat) : List Int := w.map fun (n : Nat) => (n : Int) - 3

@[expose] noncomputable def okW (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun n _ ih => andB (Nat.ble n 6) (andB (notB (Nat.beq n 3)) ih)) w

@[expose] noncomputable def okWs (us : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun u _ ih => andB (okW u) ih) us

@[expose] noncomputable def regs (mul : Nat → Nat → Nat) (R : Int → Nat) (ONE : Nat) :
    List (List Nat) → (List (Nat × Nat) → Bool) → Bool :=
  List.rec (motive := fun _ => (List (Nat × Nat) → Bool) → Bool) (fun k => k [])
    (fun u _ ih k => strictB (wgoR mul R (decW u) ONE) fun s =>
      strictB (wgoR mul R (invW (decW u)) ONE) fun si => ih fun l => k ((s, si) :: l))

@[expose] noncomputable def getP (d : Nat × Nat) (l : List (Nat × Nat)) : Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat × Nat) (fun _ => d)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat × Nat) x (fun j _ => ih j) i) l

@[expose] noncomputable def goT (mul : Nat → Nat → Nat) (b ONE : Nat) (L : List (Nat × Nat))
    (t : List (Nat × Nat)) : List Nat → (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => List Nat → (List Nat → Bool) → Bool) (fun acc k => k acc)
    (fun e _ ih acc k => strictB (mul (mul (getP (ONE, ONE) L e.2).1 (getN b acc e.1))
      (getP (ONE, ONE) L e.2).2) fun x => ih (x :: acc) k) t

@[expose] noncomputable def incrV (vec : Nat → Nat → Nat) (u b : Nat) (l : List Nat)
    (ord : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun i _ ih prev => strictB (vec u (getN b l i)) fun x => andB (Nat.blt prev x) (ih x)) ord

@[expose] noncomputable def allC (mul : Nat → Nat → Nat) (y : Nat) (L : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => andB (Nat.beq (mul p.1 y) (mul y p.1)) ih) L

@[expose] noncomputable def fib (mul vec : Nat → Nat → Nat) (vldV : Nat → Bool)
    (A B Bi ONE : Nat) (w1 w2 wi wj : List Int) (c : List Nat) (us : List (List Nat))
    (u N : Nat) (t : List (Nat × Nat)) (ord : List Nat) : Bool :=
  andB (okW c) (andB (okWs us) (
  strictB (wprod mul A B Bi ONE w1) fun g1 =>
  strictB (wprod mul A B Bi ONE (invW w1)) fun g1i =>
  strictB (wprod mul A B Bi ONE w2) fun g2 =>
  strictB (wprod mul A B Bi ONE (invW w2)) fun g2i =>
  andB (Nat.beq (mul A g1) (mul g1 A)) (andB (Nat.beq (mul A g2) (mul g2 A)) (
  strictB (wprod mul A B Bi ONE (wi ++ 1 :: invW wi)) fun bi =>
  strictB (wprod mul A B Bi ONE (wj ++ 1 :: invW wj)) fun bj =>
  strictB (mul (mul bi A) bi) fun y =>
  strictB (wgoR mul (ltr3 A g1 g1i g2 g2i) (decW c) ONE) fun cc =>
  andB (Nat.beq (mul y cc) (mul cc bj)) (
  regs mul (ltr3 A g1 g1i g2 g2i) ONE us fun L =>
  andB (allC mul y L) (andB (vldV u) (andB (Nat.beq ord.length N)
    (goT mul bi ONE L t [bi] fun l => incrV vec u bi l ord 0))))))))

end CFSG.KC.HNFFib

end
