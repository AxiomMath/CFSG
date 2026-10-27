module

public import Certificates.Data.Kernel.SporSch.PairJ3Cnt

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def scanJAt (w NR NL : Nat) (LT PT : Nat → Nat) (bs : List Nat) (c : Nat)
    (X Z ZI : Nat → Nat) (i : Nat) : Nat :=
  nIf(Nat.blt i c, strictN (nfX (nat_lit 4) (X i)) (fun x =>
    nIf(bAnd(ordPL bs (fun b => nfPtT w NR NL LT PT (nat_lit 4) x (Z b)) (nat_lit 3),
      bAnd(ord9L bs (fun b => Z (nfPtT w NR NL LT PT (nat_lit 4) x
          (ZI (nfPtT w NR NL LT PT (nat_lit 4) x b)))),
        ordPL bs (fun b => Z (Z (Z (nfPtT w NR NL LT PT (nat_lit 4) x (Z b))))) (nat_lit 17))),
      nat_lit 1, nat_lit 0)), nat_lit 0)

@[expose] noncomputable def scanJR (w NR NL : Nat) (LT PT : Nat → Nat) (bs : List Nat) (c : Nat)
    (X Z ZI : Nat → Nat) (lo len : Nat) : Nat :=
  sumN len (fun j => scanJAt w NR NL LT PT bs c X Z ZI (Nat.add lo j))

end CFSG.KS.SporSch

end
