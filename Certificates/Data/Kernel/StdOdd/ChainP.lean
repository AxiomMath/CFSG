module

public import Certificates.Data.Kernel.StdOdd.Chain

public section

namespace CFSG.KC.StdOdd.ChainP

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain

@[expose] noncomputable def packP (U : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.add x (Nat.shiftLeft ih (nat_lit 156))) U

@[expose] noncomputable def mulPA (c0 : Nat) : Nat → Nat → Nat → Nat → Nat :=
  fun n => Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ ih M P acc =>
      forceN (Nat.xor acc (Nat.mul (Nat.land M c0) (Nat.land P (full (nat_lit 156))))) fun acc' =>
        ih (Nat.shiftRight M (nat_lit 1)) (Nat.shiftRight P (nat_lit 156)) acc') n

@[expose] noncomputable def mulP (c0 M P : Nat) : Nat := mulPA c0 (nat_lit 156) M P (nat_lit 0)

@[expose] noncomputable def letP (c0 P : Nat) (Ms ms : List Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => nat_lit 0)
    (fun M _ ih ms => List.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun m ms' _ => Nat.xor (Nat.land (Nat.mul (Nat.land m (full (nat_lit 156))) c0)
        (mulP c0 M P)) (ih ms')) ms) Ms ms

@[expose] noncomputable def stepP (c0 : Nat) (Ms ms : List Nat) (P : Nat) : Nat :=
  forceN (Nat.mul (Nat.land (orL ms) (full (nat_lit 156))) c0) fun oR =>
    Nat.xor (Nat.xor P (Nat.land P oR)) (letP c0 P Ms ms)

@[expose] noncomputable def walkP (c0 : Nat) (Ms : List Nat) (S : List (List Nat)) (P : Nat)
    (k : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun P => k P)
    (fun ms _ ih P => andB (andB (Nat.beq (lenN ms) (lenN Ms)) (disjL ms))
      (forceB (stepP c0 Ms ms P) ih)) S P

@[expose] noncomputable def unpackP (P : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih P =>
      List.cons (Nat.land P (full (nat_lit 156))) (ih (Nat.shiftRight P (nat_lit 156))))
    (nat_lit 156) P

@[expose] noncomputable def bdB (U : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih => andB (Nat.blt x (Nat.shiftLeft (nat_lit 1) (nat_lit 156))) ih) U

@[expose] noncomputable def c0P : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun _ ih => Nat.add (nat_lit 1) (Nat.shiftLeft ih (nat_lit 156))) (nat_lit 156)

end CFSG.KC.StdOdd.ChainP

end
