module

public import Certificates.Data.SmithECheck

public section

namespace CFSG.SmithE.K

@[expose] noncomputable def ptBits (m : Nat) : List Nat → Nat :=
  fun L => List.rec (motive := fun _ => Nat) 0
    (fun p _ ih => (bif m.testBit p then 1 else 0) + 2 * ih) L

@[expose] noncomputable def ptChunkK (M P L : List Nat) (s n : Nat) : Bool :=
  (List.range' s n).all fun i => P.getD i 0 == ptBits (M.getD i 0) L

@[expose] noncomputable def cntK (f : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih x => bif x == 0 then 0 else ih (x &&& (x - 1)) + 1) f

@[expose] noncomputable def d2RowK (P : List Nat) (a : Nat) : Bool :=
  (P.countP fun b => cntK 693 (a &&& b) == 1) == 336

@[expose] noncomputable def d2ChunkK (P : List Nat) (s n : Nat) : Bool :=
  (List.range' s n).all fun i => d2RowK P (P.getD i 0)

end CFSG.SmithE.K
