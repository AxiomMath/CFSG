module

public import Certificates.Data.Kernel.J4Slp

public section

namespace CFSG.KC.J4Slp

open CFSG.KC.J4Q CFSG.KC.Loop

@[expose] noncomputable def forceB (l : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k List.nil)
    (fun x _ ih k => strictB x fun a => ih fun t => k (List.cons a t)) l k

@[expose] def initKN (one A Ai B Bi n : Nat) : List Nat :=
  [one, one, A, Ai, B, Bi] ++ List.replicate (2 * (n - 3)) one

@[expose] noncomputable def neK (rm x y : Nat) : Bool :=
  (List.range 112).any fun t => (List.range 112).any fun j =>
    (vecJ rm (1 <<< t) x).testBit j != (vecJ rm (1 <<< t) y).testBit j

end CFSG.KC.J4Slp

end
