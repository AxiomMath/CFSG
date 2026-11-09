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

@[expose] noncomputable def preP (f Z ZI : Nat → Nat) (a1 a0 : Nat) : Bool :=
  Nat.beq (f (Z (f (Z (f (Z a1)))))) (ZI (f (ZI (f (ZI a0)))))

@[expose] noncomputable def scanHeP (w NR NL : Nat) (LT PT : Nat → Nat) (bs : List Nat) (c : Nat)
    (X K Z ZI : Nat → Nat) (n D1 D0 i : Nat) : Nat :=
  nIf(Nat.blt i c, strictN (nfX (nat_lit 5) (X i)) (fun x => strictN (K i) (fun k =>
    nIf(preP (nfPtT w NR NL LT PT (nat_lit 5) x) Z ZI (Nat.mod (Nat.div k D1) n)
        (Nat.mod (Nat.div k D0) n),
      scanHeAt w NR NL LT PT bs c X Z ZI i, nat_lit 0))), nat_lit 0)

@[expose] noncomputable def scanHePR (w NR NL : Nat) (LT PT : Nat → Nat) (bs : List Nat) (c : Nat)
    (X K Z ZI : Nat → Nat) (n D1 D0 lo len : Nat) : Nat :=
  sumN len (fun j => scanHeP w NR NL LT PT bs c X K Z ZI n D1 D0 (Nat.add lo j))

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

@[expose] noncomputable def heoPack (L w : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun m acc => Nat.add acc (Nat.shiftLeft (f m) (Nat.mul w m))) L

@[expose] noncomputable def heoMap (L w : Nat) (Z : Nat → Nat) (V : Nat) : Nat :=
  heoPack L w (fun m => Z fld(V, Nat.mul w m, mask w))

@[expose] noncomputable def heoIx (L k c : Nat) : Nat :=
  Nat.add (Nat.sub c (Nat.mod c L)) (Nat.mod (Nat.add (Nat.mod c L) (Nat.sub L k)) L)

@[expose] noncomputable def heoRd (L w V k c : Nat) : Nat :=
  fld(V, Nat.mul w (heoIx L k c), mask w)

@[expose] noncomputable def heoLoop (n L N w mw MB : Nat) (bs : List Nat) (Z KS : Nat → Nat)
    (j : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih k V => bAnd(Nat.beq (KS (Nat.add (Nat.mul j L) k))
        (keyL n (fun b => heoRd L w V k fld(MB, Nat.mul mw b, mask mw)) bs),
      strictB (heoMap N w Z V) (fun V' => ih (Nat.succ k) V')))

@[expose] noncomputable def heoAt (w NR NL : Nat) (LT PT : Nat → Nat) (lv n L N mw MB OP : Nat)
    (bs : List Nat) (X Z KS : Nat → Nat) (j : Nat) : Bool :=
  strictB (nfX lv (X j)) (fun x =>
    strictB (heoPack N w (fun m => nfPtT w NR NL LT PT lv x fld(OP, Nat.mul w m, mask w)))
      (fun V => heoLoop n L N w mw MB bs Z KS j L (nat_lit 0) V))

end CFSG.KS.SporSch

end
