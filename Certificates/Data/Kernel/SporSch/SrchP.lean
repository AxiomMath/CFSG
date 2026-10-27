module

public import Certificates.Data.Kernel.SporSch.PairJ3Cnt

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def srchPAt (w kS NR NL : Nat) (LT PT QT LR : Nat → Nat) (bs : List Nat)
    (b0 : Nat) (X Y : Nat → Nat) (Fl : (Nat → Nat) → Bool) (k0 : Nat) : Nat :=
  strictN (trInvPtT w kS NR NL LT PT (nat_lit 0) k0 (Y (trPtT w NR NL LT PT (nat_lit 0) k0 b0)))
    (fun u => strictN (lvT NL w QT (nat_lit 1) u) (fun k1 =>
    nIf(Nat.blt k1 (rcnt (LR (nat_lit 1))),
      foldUp (rcnt (LR (nat_lit 2))) (fun k2 s => foldUp (rcnt (LR (nat_lit 3))) (fun k3 s =>
        strictN (nf4 k0 k1 k2 k3) (fun F =>
          nIf(bAnd(eqOnL bs (fun b => nfPtT w NR NL LT PT (nat_lit 4) F (X b))
              (fun b => Y (nfPtT w NR NL LT PT (nat_lit 4) F b)),
            Fl (fun b => nfPtT w NR NL LT PT (nat_lit 4) F b)), Nat.succ s, s))) s) (nat_lit 0),
      nat_lit 0)))

@[expose] noncomputable def srchPR (w kS NR NL : Nat) (LT PT QT LR : Nat → Nat) (bs : List Nat)
    (b0 : Nat) (X Y : Nat → Nat) (Fl : (Nat → Nat) → Bool) (lo len : Nat) : Nat :=
  sumN len (fun j => srchPAt w kS NR NL LT PT QT LR bs b0 X Y Fl (Nat.add lo j))

end CFSG.KS.SporSch

end
