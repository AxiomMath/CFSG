module

public import Certificates.Kernel.Co1M.D10073
public import Certificates.Data.Kernel.Co1M.Odd73

public section

namespace CFSG.KD.Co1M

open CFSG.KLie.CT CFSG.KC.SortTree

@[expose] noncomputable def S73L (b : Nat) : Nat :=
  nIf(Nat.blt b (nat_lit 2859), S73L0 b,
    nIf(Nat.blt b (nat_lit 5718), S73L1 (Nat.sub b (nat_lit 2859)),
      nIf(Nat.blt b (nat_lit 8577), S73L2 (Nat.sub b (nat_lit 5718)),
        S73L3 (Nat.sub b (nat_lit 8577)))))

@[expose] noncomputable def S73tab (i : Nat) : Nat := recT S73L (nat_lit 4) (nat_lit 602) i

@[expose] noncomputable def A73tab (i : Nat) : Nat := recT A73L (nat_lit 6) (nat_lit 83) i

@[expose] noncomputable def t73K (lo cnt : Nat) : Bool :=
  CFSG.KC.InvFam.chunksK (CFSG.KC.Odd73.act73 R73) (nat_lit 14)
    (CFSG.KC.Co1F2.getL (nat_lit 0) R73 (nat_lit 27)) S73tab (nat_lit 182919) (nat_lit 576)
    (nat_lit 4) (nat_lit 18) (nat_lit 64) lo cnt

@[expose] noncomputable def a73K (lo cnt : Nat) : Bool :=
  allN cnt fun j => (fun c => CFSG.KC.Odd73.auxRun73 R73 S73tab A73tab (nat_lit 576) (nat_lit 4)
    (nat_lit 18) (Nat.mul c (nat_lit 64)) (cntF (nat_lit 182919) (nat_lit 64) (Nat.mul c (nat_lit 64))))
    (Nat.add lo j)

@[expose] noncomputable def ta73S (q : Nat) : Bool :=
  andB (t73K (Nat.mul q (nat_lit 16)) (nat_lit 16)) (a73K (Nat.mul q (nat_lit 16)) (nat_lit 16))

end CFSG.KD.Co1M

end
