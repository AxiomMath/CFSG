module

public import Init

public section

namespace CFSG.KC.Co2Mem

@[expose] noncomputable def cntK (N : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (f k))) N

end CFSG.KC.Co2Mem

end
