module

public import Certificates.Data.Kernel.SporSch.PairJ3Cnt

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def ord10L (bs : List Nat) (f : Nat → Nat) : Bool :=
  bAnd(eqOnL bs (powF f (nat_lit 10)) (fun x => x),
    bAnd(bIf(eqOnL bs (powF f (nat_lit 5)) (fun x => x), false, true),
      bIf(eqOnL bs (powF f (nat_lit 2)) (fun x => x), false, true)))

@[expose] noncomputable def scanWAt (w NR NL : Nat) (LT PT : Nat → Nat) (bs : List Nat) (c : Nat)
    (X Z ZI : Nat → Nat) (i : Nat) : Nat :=
  nIf(Nat.blt i c, strictN (nfX (nat_lit 4) (X i)) (fun x =>
    nIf(bAnd(ordPL bs (fun b => nfPtT w NR NL LT PT (nat_lit 4) x (Z b)) (nat_lit 5),
      bAnd(ordPL bs (fun b => Z (nfPtT w NR NL LT PT (nat_lit 4) x
          (ZI (nfPtT w NR NL LT PT (nat_lit 4) x b)))) (nat_lit 5),
        ord10L bs (fun b => Z (nfPtT w NR NL LT PT (nat_lit 4) x (Z b))))),
      nat_lit 1, nat_lit 0)), nat_lit 0)

@[expose] noncomputable def scanWR (w NR NL : Nat) (LT PT : Nat → Nat) (bs : List Nat) (c : Nat)
    (X Z ZI : Nat → Nat) (lo len : Nat) : Nat :=
  sumN len (fun j => scanWAt w NR NL LT PT bs c X Z ZI (Nat.add lo j))

end CFSG.KS.SporSch

end
