module

public import Certificates.Data.Kernel.MonsterB.Co2Perm

public section

namespace CFSG.KC.Co2Mem

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def letterK (P PI : Nat → Nat) (l : Int) (x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (pg 12 (mask 12) (PI (Nat.sub l.natAbs 1)) x)
    (pg 12 (mask 12) (P (Nat.sub l.natAbs 1)) x) (decide (0 < l))

@[expose] noncomputable def wordK (P PI : Nat → Nat) (w : List Int) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun l _ ih x => ih (letterK P PI l x)) w

@[expose] noncomputable def iterK (f : Nat → Nat) (e x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ y => f y) e

@[expose] noncomputable def permF (n : Nat) (g : Nat → Nat) (k : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun t r => permStep n (g t) r) k

end CFSG.KC.Co2Mem

end
