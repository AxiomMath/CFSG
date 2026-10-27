module

public import Certificates.Data.Kernel.HNF26720K

public section

namespace CFSG.KC.HNF26729

open CFSG.KC.Ord CFSG.KC.HNF26720

@[expose] noncomputable def ltr3 {α : Type} (A G1 G1i G2 G2i : α) (l : Int) : α :=
  Int.rec (motive := fun _ => α)
    (fun n => Bool.rec (motive := fun _ => α)
      (Bool.rec (motive := fun _ => α) G2 G1 (Nat.beq n 2)) A (Nat.beq n 1))
    (fun n => Bool.rec (motive := fun _ => α)
      (Bool.rec (motive := fun _ => α) G2i G1i (Nat.beq n 1)) A (Nat.beq n 0)) l

@[expose] noncomputable def wgoR (mul : Nat → Nat → Nat) (R : Int → Nat) (w : List Int) :
    Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => CFSG.KC.Loop.strictN (mul acc (R l)) ih) w

@[expose] noncomputable def getN (d : Nat) (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => d)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) l

@[expose] noncomputable def go (vec : Nat → Nat → Nat) (v S0 S1 : Nat) (t : List (Nat × Nat)) :
    List Nat → (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => List Nat → (List Nat → Bool) → Bool) (fun acc k => k acc)
    (fun e _ ih acc k => strictB (vec (getN v acc e.1) (nIf(Nat.beq e.2 0, S0, S1)))
      fun u => ih (u :: acc) k) t

@[expose] noncomputable def incrK (v : Nat) (l : List Nat) (ord : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun i _ ih prev => strictB (getN v l i) fun x => andB (Nat.blt prev x) (ih x)) ord

@[expose] noncomputable def orbOK (vec : Nat → Nat → Nat) (vldV : Nat → Bool) (v S0 S1 N : Nat)
    (t : List (Nat × Nat)) (ord : List Nat) : Bool :=
  andB (vldV v) (andB (Nat.beq ord.length N) (go vec v S0 S1 t [v] fun l => incrK v l ord 0))

@[expose] noncomputable def full (mul vec : Nat → Nat → Nat) (vldV : Nat → Bool)
    (A B Bi ONE : Nat) (w1 w2 w8 u0 u1 : List Int) (v N : Nat) (t : List (Nat × Nat))
    (ord : List Nat) : Bool :=
  strictB (wprod mul A B Bi ONE w1) fun g1 =>
  strictB (wprod mul A B Bi ONE (invW w1)) fun g1i =>
  strictB (wprod mul A B Bi ONE w2) fun g2 =>
  strictB (wprod mul A B Bi ONE (invW w2)) fun g2i =>
  strictB (wgoR mul (ltr3 A g1 g1i g2 g2i) u0 ONE) fun s0 =>
  strictB (wgoR mul (ltr3 A g1 g1i g2 g2i) u1 ONE) fun s1 =>
  strictB (wprod mul A B Bi ONE (w8 ++ 1 :: invW w8)) fun bt =>
  andB (Nat.beq (mul s0 bt) (mul bt s0)) (andB (Nat.beq (mul s1 bt) (mul bt s1))
    (orbOK vec vldV v s0 s1 N t ord))

end CFSG.KC.HNF26729

end
