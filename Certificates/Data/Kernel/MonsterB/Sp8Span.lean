module

public import Certificates.Data.Kernel.MonsterB.Rep4371Row

public section

namespace CFSG.KC.Sp8Span

open CFSG.KC CFSG.KC.KDense CFSG.KC.Loop CFSG.KC.Rep4371Row

@[expose] def spanRows : List Nat :=
  0 :: ((List.range 12).map fun i => 2 ^ i) ++
    (List.range 12).flatMap fun j => (List.range j).map fun i => 2 ^ i + 2 ^ j

@[expose] noncomputable def chainT : List (Nat → Nat → Nat) → Nat → Nat → Nat
  | [], η, c => enc 0 η c
  | t :: ts, η, c => ts.foldl (fun r f => thenT f r) (t η c)

@[expose] noncomputable def spanEqT (L R : List (Nat → Nat → Nat)) : Bool :=
  spanRows.all fun c =>
    Nat.beq (chainT L 0 c) (chainT R 0 c) && Nat.beq (chainT L 1 c) (chainT R 1 c)

end CFSG.KC.Sp8Span

end
