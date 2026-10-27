module

public import Certificates.Data.Kernel.U6.F2K

public section

namespace CFSG.KC.U6F2

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def c2CL : List Nat := [1, 2, 3, 4, 10, 11, 12, 13, 5, 6, 7, 8, 14, 15, 16, 17]

@[expose] noncomputable def c2IL : List Nat :=
  [16, 0, 1, 2, 3, 8, 9, 10, 11, 16, 4, 5, 6, 7, 12, 13, 14, 15]

@[expose] noncomputable def blk2K (X : Nat) : Nat :=
  strictN X fun X => orN 32 fun k =>
    nIf(bit X (Nat.add (nIf(Nat.blt k 16, 0, 162)) (getLD 0 c2CL (Nat.mod k 16))), pw2 k, 0)

@[expose] noncomputable def emb2K (d : Nat) : Nat :=
  strictN d fun d => orN 18 fun c => (fun i => nIf(Nat.blt i 16,
    Nat.lor (nIf(bit d i, pw2 c, 0)) (nIf(bit d (Nat.add 16 i), pw2 (Nat.add 162 c), 0)), 0))
      (getLD 0 c2IL c)

@[expose] noncomputable def parK (w n : Nat) : Bool :=
  CFSG.KC.M1F2.strictB n fun n => Nat.rec (motive := fun _ => Bool) false
    (fun i acc => Bool.rec (motive := fun _ => Bool) acc (notB acc) (bit n i)) w

end CFSG.KC.U6F2

end
