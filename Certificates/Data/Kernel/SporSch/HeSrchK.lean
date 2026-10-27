module

public import Certificates.Data.Kernel.SporSch.HeSrch

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def srchAK1 (w kS NR NL : Nat) (LT PT QT LR : Nat → Nat) (bs : List Nat)
    (X Y : Nat → Nat) (k0 k1 s : Nat) : Nat :=
  strictN (trPtT w NR NL LT PT (nat_lit 0) k0 (rpt w (mask w) (LR (nat_lit 1)) k1)) (fun q =>
  strictN (trInvPtT w kS NR NL LT PT (nat_lit 1) k1
    (trInvPtT w kS NR NL LT PT (nat_lit 0) k0 (Y q))) (fun v =>
  strictN (lvT NL w QT (nat_lit 2) v) (fun k2 =>
  nIf(Nat.blt k2 (rcnt (LR (nat_lit 2))),
    foldUp (rcnt (LR (nat_lit 3))) (fun k3 s => foldUp (rcnt (LR (nat_lit 4))) (fun k4 s =>
      strictN (nf5 k0 k1 k2 k3 k4) (fun F =>
        nIf(eqOnL bs (fun b => nfPtT w NR NL LT PT (nat_lit 5) F (X b))
            (fun b => Y (nfPtT w NR NL LT PT (nat_lit 5) F b)), Nat.succ s, s))) s) s,
    s))))

@[expose] noncomputable def srchAK (w kS NR NL : Nat) (LT PT QT LR : Nat → Nat) (bs : List Nat)
    (b0 : Nat) (X Y : Nat → Nat) (k0 lo len : Nat) : Nat :=
  strictN (trPtT w NR NL LT PT (nat_lit 0) k0 b0) (fun p0 =>
  nIf(Nat.beq (Y p0) p0,
    foldUp len (fun j s => nIf(Nat.blt (Nat.add lo j) (rcnt (LR (nat_lit 1))),
      srchAK1 w kS NR NL LT PT QT LR bs X Y k0 (Nat.add lo j) s, s)) (nat_lit 0),
    nat_lit 0))

end CFSG.KS.SporSch

end
