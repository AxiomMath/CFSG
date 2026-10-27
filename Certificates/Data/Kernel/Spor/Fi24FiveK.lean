module

public import Certificates.Data.Kernel.Spor.Fi24Base
public import Certificates.Data.Kernel.Spor.Fi24PumpK
public import Certificates.Data.Kernel.Spor.Fi24Kn

public section

namespace CFSG.KC.Fi24FiveK

open CFSG.KC.Fi24PumpK CFSG.KC.Fi24Kn

@[expose] noncomputable def allLt (W : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun w _ ih => letLt w && ih) W

@[expose] noncomputable def catW (W : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun w _ ih => w ++ ih) W

@[expose] noncomputable def expC (M : List (List Nat)) (c : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun k _ ih => nthW M k ++ ih) c

@[expose] noncomputable def lenLe (W : List (List Nat)) (n : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ _ ih n => Nat.rec (motive := fun _ => Bool) false (fun m _ => ih m) n) W n

@[expose] noncomputable def commB (E : List Nat → List Nat → Bool) (u v : List Nat) : Bool :=
  E (u ++ v) (v ++ u)

@[expose] noncomputable def letOK (E : List Nat → List Nat → Bool) (M : List (List Nat)) (j : Nat) :
    Bool :=
  E (nthW M (2 * j) ++ nthW M (2 * j + 1)) [] &&
    (commB E (nthW M (2 * j)) (nthW M 0) || commB E (nthW M (2 * j)) (nthW M 2))

@[expose] noncomputable def stageOK (E : List Nat → List Nat → Bool) (M C R : List (List Nat))
    (k : Nat) : Bool :=
  letLt (nthW R k) && E (expC M (nthW C k)) (nthW R k)

@[expose] noncomputable def headOK (E : List Nat → List Nat → Bool) (M : List (List Nat))
    (H : List Nat) (R : List (List Nat)) (n : Nat) : Bool :=
  lenLe M 34 && lenLe R n && allLt M && letLt H &&
    E (repW (nthW M 0) 5) [] && E (repW (nthW M 2) 5) [] && !E (nthW M 0) [] &&
    commB E (nthW M 0) (nthW M 2) && E (nthW M 0 ++ H) (H ++ nthW M 2) && commB E [0] (nthW M 2)

@[expose] noncomputable def bOK (E : List Nat → List Nat → Bool) (R : List (List Nat)) : Bool :=
  E (catW R) [2]

end CFSG.KC.Fi24FiveK

end
