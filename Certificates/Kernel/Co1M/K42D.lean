module

public import Certificates.Kernel.Co1M.D10042
public import Certificates.Kernel.Co1M.Data10041
public import Certificates.Data.Kernel.CosetBfsK
public import Certificates.Data.Kernel.SortTree

public section

namespace CFSG.KD.Co1M

open CFSG.KLie.CT CFSG.KC.SortTree CFSG.KC.BfsT CFSG.KC.M1F2 CFSG.KC.Co1F2

@[expose] noncomputable def act42 (g v : Nat) : Nat :=
  canonK (nat_lit 2) (nat_lit 4) (vmF (nat_lit 24) (getL (nat_lit 0) [CT0, CT1, CT2] g) v)

@[expose] noncomputable def C42tab (i : Nat) : Nat := recT C42L (nat_lit 6) (nat_lit 50) i

@[expose] noncomputable def t42K (lo cnt : Nat) : Bool :=
  allN cnt fun j => chunkOK act42 (nat_lit 3) (fun _ => true) (nat_lit 40) C42tab (nat_lit 498960)
    (nat_lit 24) (nat_lit 5) (nat_lit 19) (nat_lit 64) (Nat.add lo j)

@[expose] noncomputable def t42S (q : Nat) : Bool := t42K (Nat.mul q (nat_lit 16)) (nat_lit 16)

end CFSG.KD.Co1M

end
