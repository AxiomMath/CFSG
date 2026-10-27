module

public import Certificates.Data.Kernel.SporSch.PairHeCnt

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def cnt234 (LR : Nat → Nat) (t : Nat → Bool) (k0 k1 : Nat) : Nat :=
  foldUp (rcnt (LR (nat_lit 2))) (fun k2 s => foldUp (rcnt (LR (nat_lit 3))) (fun k3 s =>
    foldUp (rcnt (LR (nat_lit 4))) (fun k4 s =>
      strictN (nf5 k0 k1 k2 k3 k4) (fun F => nIf(t F, Nat.succ s, s))) s) s) (nat_lit 0)

@[expose] noncomputable def cnt0R (LR : Nat → Nat) (t : Nat → Bool) (lo len : Nat) : Nat :=
  sumN len (fun j => cnt234 LR t (nat_lit 0) (Nat.add lo j))

@[expose] noncomputable def srchAAt (w kS NR NL : Nat) (LT PT QT LR : Nat → Nat) (bs : List Nat)
    (b0 : Nat) (X Y : Nat → Nat) (k0 : Nat) : Nat :=
  strictN (trPtT w NR NL LT PT (nat_lit 0) k0 b0) (fun p0 =>
  nIf(Nat.beq (Y p0) p0,
    foldUp (rcnt (LR (nat_lit 1))) (fun k1 s =>
      strictN (trPtT w NR NL LT PT (nat_lit 0) k0 (rpt w (mask w) (LR (nat_lit 1)) k1)) (fun q =>
      strictN (trInvPtT w kS NR NL LT PT (nat_lit 1) k1
        (trInvPtT w kS NR NL LT PT (nat_lit 0) k0 (Y q))) (fun v =>
      strictN (lvT NL w QT (nat_lit 2) v) (fun k2 =>
      nIf(Nat.blt k2 (rcnt (LR (nat_lit 2))),
        foldUp (rcnt (LR (nat_lit 3))) (fun k3 s => foldUp (rcnt (LR (nat_lit 4))) (fun k4 s =>
          strictN (nf5 k0 k1 k2 k3 k4) (fun F =>
            nIf(eqOnL bs (fun b => nfPtT w NR NL LT PT (nat_lit 5) F (X b))
                (fun b => Y (nfPtT w NR NL LT PT (nat_lit 5) F b)), Nat.succ s, s))) s) s,
        s))))) (nat_lit 0),
    nat_lit 0))

@[expose] noncomputable def srchAR (w kS NR NL : Nat) (LT PT QT LR : Nat → Nat) (bs : List Nat)
    (b0 : Nat) (X Y : Nat → Nat) (lo len : Nat) : Nat :=
  sumN len (fun j => srchAAt w kS NR NL LT PT QT LR bs b0 X Y (Nat.add lo j))

@[expose] noncomputable def twK (w NR NL : Nat) (LT PT : Nat → Nat) (bs : List Nat) (U : Nat → Nat)
    (F : Nat) : Bool :=
  eqOnL bs (fun b => U (nfPtT w NR NL LT PT (nat_lit 5) F (U (nfPtT w NR NL LT PT (nat_lit 5) F b))))
    (fun b => b)

end CFSG.KS.SporSch

end
