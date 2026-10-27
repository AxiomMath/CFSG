module

public import Certificates.Data.Kernel.FiveStdKList
public import Certificates.Data.Kernel.FiveStdKDiag

public section

namespace CFSG.KC.FiveStdK

@[expose] noncomputable def memL (L : List Nat) (c : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => orB (Nat.beq x c) ih) L

@[expose] noncomputable def swapsKK (K1 K2 : List Nat) (c : Nat) : Bool :=
  letB (invK c) fun ci => allL K1 fun x => memL K2 (cjK c ci x)

@[expose] noncomputable def normKK (K1 : List Nat) (c : Nat) : Bool :=
  letB (invK c) fun ci => allL K1 fun x => memL K1 (cjK c ci x)

@[expose] noncomputable def pairCondK (S0s S0n : List Nat) (t u : Nat) : Bool :=
  S0s.contains t && S0n.contains u && ordK t == 2 && ordK u == 2 && !(Nat.beq u zK) &&
    Nat.beq (mulK t u) (mulK u t)

@[expose] noncomputable def cwOK (R : List (Nat × Nat)) (e : Nat × Nat × Nat × Nat) : Bool :=
  Nat.blt e.2.2.1 4 && validK e.2.2.2 && Nat.beq (fS e.2.2.2) 0 &&
    Nat.beq (cjK e.2.2.2 (invK e.2.2.2) (R.getD e.2.2.1 (0, 0)).1) e.1 &&
    Nat.beq (cjK e.2.2.2 (invK e.2.2.2) (R.getD e.2.2.1 (0, 0)).2) e.2.1

end CFSG.KC.FiveStdK

end
