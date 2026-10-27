module

public import Certificates.Data.Kernel.KDenseP.Plan

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.KDense CFSG.Monster.AxisCount

@[expose] noncomputable def unpack24 (c : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih x => List.cons (Nat.land x (nat_lit 31)) (ih (Nat.shiftRight x (nat_lit 5)))) (nat_lit 24) c

@[expose] noncomputable def decG (c : Nat) : Native.Gen :=
  (fun k v => Bool.rec (motive := fun _ => Native.Gen)
    (Bool.rec (motive := fun _ => Native.Gen)
      (Bool.rec (motive := fun _ => Native.Gen) Native.Gen.tau Native.Gen.xi (Nat.beq k (nat_lit 3)))
      (Native.Gen.sign v) (Nat.beq k (nat_lit 2)))
    (Bool.rec (motive := fun _ => Native.Gen) (Native.Gen.perm (List.toArray (unpack24 v)))
      (Native.Gen.rho (Nat.beq (Nat.land v (nat_lit 1)) (nat_lit 1), Nat.land (Nat.shiftRight v (nat_lit 1)) (nat_lit 4095),
        Nat.shiftRight v (nat_lit 13)))
      (Nat.beq k (nat_lit 0)))
    (Nat.blt k (nat_lit 2)))
  (Nat.land c (nat_lit 7)) (Nat.shiftRight c (nat_lit 3))

@[expose] noncomputable def decW (l : List Nat) : List Native.Gen :=
  List.rec (motive := fun _ => List Native.Gen) [] (fun c _ ih => List.cons (decG c) ih) l

@[expose] noncomputable def wordEqB (u v : List Native.Gen) : Bool :=
  List.rec (motive := fun _ => List Native.Gen → Bool)
    (fun v' => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) v')
    (fun g _ ih v' => List.rec (motive := fun _ => Bool) false (fun h t _ => andB (genEq g h) (ih t)) v') u v

@[expose] noncomputable def wordsEqB (W : Nat → List Nat) (words : Nat → List Native.Gen) (N : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun σ ih => andB (wordEqB (decW (W σ)) (words σ)) ih) N

end CFSG.KC.KDenseP

end
