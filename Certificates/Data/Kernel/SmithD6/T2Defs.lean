module

public import Certificates.Data.SmithD6Model
public import Certificates.Data.Kernel.PkTree

public section

namespace CFSG.KC.SmithD6T2

open CFSG.SmithD6 CFSG.KC.PkTree CFSG.KC.Loop

@[expose] def d6GenPairs : List (Nat × Nat) :=
  [(eV 0, eV 1)] ++
    ((List.range 5).flatMap fun i => [(eV i, fV (i + 1)), (fV i, eV (i + 1))]) ++
    [(eV 4, eV 5), (fV 4, fV 5)]

@[expose] def d6GenPair (g : Nat) : Nat × Nat := d6GenPairs.getD g (0, 0)

@[expose] def d6Step (g x : Nat) : Nat := sgl (d6GenPair g).1 (d6GenPair g).2 x

@[expose] def d6IsPt (x : Nat) : Bool := !(x == 0) && !qf x

@[expose] def d6IsRs (x : Nat) : Bool := !(x == 0) && !(x == 1) && !qf x && !bf 1 x

@[expose] def d6FixE0 (g : Nat) : Bool := Nat.blt g 13 && d6Step g 1 == 1

@[expose] noncomputable def d6PtTreeOK (D G : Nat) : Bool :=
  pkTreeOK 4096 64 5 4 D G d6IsPt (· == 1) (Nat.blt · 13) d6Step

@[expose] noncomputable def d6RsTreeOK (D G : Nat) : Bool :=
  pkTreeOK 4096 64 5 4 D G d6IsRs (· == 2) d6FixE0 d6Step

@[expose] noncomputable def d6SplitAt (S w : Nat) : Bool :=
  bf 1 w || !qf w ||
    (fun s => !(s == 0) && !qf s && !bf 1 s && bf w s) (pkGet S 12 w)

@[expose] noncomputable def d6SplitOK (S : Nat) : Bool := allBelow 4096 64 (d6SplitAt S)

@[expose] noncomputable def d6PtCnt : Nat := sumBelow 4096 64 fun x => if d6IsPt x then 1 else 0

@[expose] noncomputable def d6RsCnt : Nat := sumBelow 4096 64 fun x => if d6IsRs x then 1 else 0

end CFSG.KC.SmithD6T2

end
