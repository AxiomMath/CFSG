module

public import Certificates.Kernel.Co1M.K73D
public import Certificates.Kernel.Co1M.K73FD
public import Certificates.Kernel.Co1M.D10045
public import Certificates.Data.Kernel.Co1M.U45

public section

namespace CFSG.KD.Co1M

open CFSG.KLie.CT CFSG.KC.SortTree CFSG.KC.Co1F2 CFSG.KC.U45

@[expose] noncomputable def st45S (q : Nat) : Bool :=
  stRun (nat_lit 4) (nat_lit 18) S73tab SI45 (Nat.mul q (nat_lit 1024))
    (cntF (nat_lit 182919) (nat_lit 1024) (Nat.mul q (nat_lit 1024)))

@[expose] noncomputable def se45K (nw : Nat) (L : List (List Nat)) : Bool :=
  allE L (stE nw (getL (nat_lit 0) R73 (nat_lit 27)) S73tab (nat_lit 182919))

@[expose] noncomputable def ce45K (nw : Nat) (L : List (List Nat)) : Bool :=
  allE L (c5E nw (getL (nat_lit 0) R73 (nat_lit 86)) S73tab A73tab (nat_lit 182919))

@[expose] noncomputable def hd45K (SE CE : List (List Nat)) : Bool :=
  andB (eqL (headsE SE) SI45) (andB (incE CE (nat_lit 0)) (Nat.beq (lenE CE) (nat_lit 759)))

@[expose] noncomputable def t45K (nw : Nat) (L : List (List Nat)) : Bool :=
  allE L fun e => andB (t4K73 (getL (nat_lit 0) e (nat_lit 2))) (t4K73 (getL (nat_lit 0) e (lastO nw)))

end CFSG.KD.Co1M

end
