module

public import Certificates.Data.Kernel.LocalQT.HSAutN

public section

namespace CFSG.KS.HSAutN

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def wfoldR (L : Nat → Nat) (ls : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idn (fun l _ ih => strictN ih (fun q => pc (L l) q)) ls

@[expose] noncomputable def lt3 (A B BI l : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), A, nIf(Nat.beq l (nat_lit 1), B, BI))

end CFSG.KS.HSAutN

end
