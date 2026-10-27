module

public import Certificates.Data.Kernel.Misc.O73

public section

namespace CFSG.SmithE.K

open CFSG.KC.Misc.O73

@[expose] noncomputable def ivFP (FP n : Nat) (l : List Nat) : Bool :=
  Nat.beq l.length n &&
  Nat.beq FP (l.foldr (fun x acc => Nat.add x (Nat.mul (2 ^ 105) acc)) 0) &&
    l.all fun x => Nat.blt x (2 ^ 105)

@[expose] noncomputable def ivLt (FP n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun v acc => acc &&
    Nat.rec (motive := fun _ => Bool) true (fun k acc' => acc' &&
      Nat.blt (at' 5 (at' 105 FP v) k) 21) 21) n

@[expose] noncomputable def ivRootK (RT : List Nat) (FP v : Nat) : Bool :=
  RT.any fun r => Nat.beq r (at' 105 FP v)

@[expose] noncomputable def ivEdgeK (FP : Nat) (SG SR : List (List Nat)) (g u v : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => acc &&
    Nat.beq (at' 5 (at' 105 FP v) k)
      ((SG.getD g []).getD (at' 5 (at' 105 FP u) ((SR.getD g []).getD k 0)) 0)) 21

end CFSG.SmithE.K
