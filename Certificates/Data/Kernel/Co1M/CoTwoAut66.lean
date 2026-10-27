module

public import Certificates.Data.Kernel.Co1M.InvFam

public section

namespace CFSG.KC.CoTwoAut

open CFSG.KLie.CT CFSG.KC.Co1F2 CFSG.KC.SortTree

@[expose] noncomputable def getT (Ts : List (Nat → Nat)) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun f _ ih j => Nat.rec (motive := fun _ => Nat → Nat) f (fun j' _ => ih j') j) Ts

@[expose] noncomputable def covAt (Ts : List (Nat → Nat)) (szs : List Nat) (P pt : Nat → Nat)
    (n i : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    ((fun p => (fun j k => andB (Nat.blt j (lenL szs)) (andB (Nat.blt k (getL (nat_lit 0) szs j))
        (Nat.beq (valF (nat_lit 24) (getT Ts j k)) (pt i))))
      (Nat.land p (nat_lit 7)) (Nat.shiftRight p (nat_lit 3))) (P i))
    (Nat.blt i n)

@[expose] noncomputable def covK (Ts : List (Nat → Nat)) (szs : List Nat) (P pt : Nat → Nat)
    (n lo cnt : Nat) : Bool :=
  allN cnt fun i => covAt Ts szs P pt n (Nat.add lo i)

end CFSG.KC.CoTwoAut

end
