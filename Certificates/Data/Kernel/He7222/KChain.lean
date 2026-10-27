module

public import Certificates.Data.Kernel.He7222.Chain
public import Certificates.Data.Kernel.He7222.Fix
public import Certificates.Data.Kernel.He7222.Cls

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow

@[expose] noncomputable def kgK (n w m idn : Nat) (Ts : List (List Nat)) (s : Nat) (G : List Nat)
    (U : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun q => Nat.beq q (lenS G))
    (fun u _ ih q => strictB (getS G q) (fun g =>
      bAnd(tupOK Ts u, bAnd(Nat.beq (tupK n w m idn Ts u) g,
        bAnd(commK n w m (Nat.mul n w) g s, strictB (Nat.succ q) ih)))))
    U (nat_lit 0)

@[expose] noncomputable def chainK (n w m idn : Nat) (G0 B : List Nat)
    (R T S Ref Nn : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → List Nat → Bool) (fun i _ => Nat.beq i (lenS B))
    (fun Ti _ ih i G => bAnd(treeK n w m idn G (getS B i) (getLs R i) Ti,
      strictB (Nat.succ i) (fun i' => bIf(Nat.blt i' (lenS B),
        bAnd(schK n w m G (getS B i) (getLs R i) Ti (getLs Ref i') (getLs Nn i) (getLs S i),
          ih i' (getLs S i)),
        ih i' G))))
    T (nat_lit 0) G0

end CFSG.KC.HeChain

end
