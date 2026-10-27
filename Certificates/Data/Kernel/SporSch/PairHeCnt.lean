module

public import Certificates.Data.Kernel.SporSch.PairJ3Cnt

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def ordDL (bs : List Nat) (f : Nat → Nat) (m : Nat) (ds : List Nat) : Bool :=
  bAnd(eqOnL bs (powF f m) (fun x => x),
    List.rec (motive := fun _ => Bool) true
      (fun d _ ih => bAnd(bIf(eqOnL bs (powF f d) (fun x => x), false, true), ih)) ds)

@[expose] noncomputable def scanHeAt (w NR NL : Nat) (LT PT : Nat → Nat) (bs : List Nat) (c : Nat)
    (X Z ZI : Nat → Nat) (i : Nat) : Nat :=
  nIf(Nat.blt i c, strictN (nfX (nat_lit 5) (X i)) (fun x =>
    nIf(bAnd(ordPL bs (fun b => nfPtT w NR NL LT PT (nat_lit 5) x (Z b)) (nat_lit 7),
      bAnd(ordDL bs (fun b => Z (nfPtT w NR NL LT PT (nat_lit 5) x
          (ZI (nfPtT w NR NL LT PT (nat_lit 5) x b)))) (nat_lit 6) [nat_lit 3, nat_lit 2],
      bAnd(ordDL bs (fun b => Z (nfPtT w NR NL LT PT (nat_lit 5) x (Z b))) (nat_lit 12)
          [nat_lit 6, nat_lit 4],
        ordDL bs (fun b => Z (Z (nfPtT w NR NL LT PT (nat_lit 5) x (Z b)))) (nat_lit 15)
          [nat_lit 5, nat_lit 3]))),
      nat_lit 1, nat_lit 0)), nat_lit 0)

@[expose] noncomputable def scanHeR (w NR NL : Nat) (LT PT : Nat → Nat) (bs : List Nat) (c : Nat)
    (X Z ZI : Nat → Nat) (lo len : Nat) : Nat :=
  sumN len (fun j => scanHeAt w NR NL LT PT bs c X Z ZI (Nat.add lo j))

@[expose] noncomputable def nf5 (k0 k1 k2 k3 k4 : Nat) : Nat :=
  Nat.lor k0 (Nat.lor (Nat.shiftLeft k1 (nat_lit 16)) (Nat.lor (Nat.shiftLeft k2 (nat_lit 32))
    (Nat.lor (Nat.shiftLeft k3 (nat_lit 48)) (Nat.shiftLeft k4 (nat_lit 64)))))

@[expose] noncomputable def srch5At (w kS NR NL : Nat) (LT PT QT LR : Nat → Nat) (bs : List Nat)
    (b0 : Nat) (X Y : Nat → Nat) (k0 : Nat) : Nat :=
  strictN (trInvPtT w kS NR NL LT PT (nat_lit 0) k0 (Y (trPtT w NR NL LT PT (nat_lit 0) k0 b0)))
    (fun u => strictN (lvT NL w QT (nat_lit 1) u) (fun k1 =>
    nIf(Nat.blt k1 (rcnt (LR (nat_lit 1))),
      foldUp (rcnt (LR (nat_lit 2))) (fun k2 s => foldUp (rcnt (LR (nat_lit 3))) (fun k3 s =>
        foldUp (rcnt (LR (nat_lit 4))) (fun k4 s =>
        strictN (nf5 k0 k1 k2 k3 k4) (fun F =>
          nIf(eqOnL bs (fun b => nfPtT w NR NL LT PT (nat_lit 5) F (X b))
              (fun b => Y (nfPtT w NR NL LT PT (nat_lit 5) F b)), Nat.succ s, s))) s) s)
        (nat_lit 0),
      nat_lit 0)))

@[expose] noncomputable def srch5R (w kS NR NL : Nat) (LT PT QT LR : Nat → Nat) (bs : List Nat)
    (b0 : Nat) (X Y : Nat → Nat) (lo len : Nat) : Nat :=
  sumN len (fun j => srch5At w kS NR NL LT PT QT LR bs b0 X Y (Nat.add lo j))

@[expose] noncomputable def bind5At (n w NR NL : Nat) (LT PT : Nat → Nat) (F P x : Nat) : Bool :=
  bIf(Nat.blt x n, Nat.beq (pg w (mask w) P x) (nfPtT w NR NL LT PT (nat_lit 5) F x), true)

end CFSG.KS.SporSch

end
