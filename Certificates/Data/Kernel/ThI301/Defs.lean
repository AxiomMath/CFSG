module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.ThI301

open CFSG.KC.Enum

@[expose] noncomputable def ncAt (x y yi p : Nat) : Bool :=
  bIf(Nat.beq (pg (nat_lit 4) (nat_lit 15) x (pg (nat_lit 4) (nat_lit 15) y
      (pg (nat_lit 4) (nat_lit 15) x (pg (nat_lit 4) (nat_lit 15) yi p))))
    (pg (nat_lit 4) (nat_lit 15) y (pg (nat_lit 4) (nat_lit 15) x
      (pg (nat_lit 4) (nat_lit 15) yi (pg (nat_lit 4) (nat_lit 15) x p)))), false, true)

@[expose] noncomputable def thRec (T : Nat → Nat) (rm : Nat) (Y YI : Nat → Nat) (i : Nat) : Bool :=
  strictB (rget T (nat_lit 0) (nat_lit 0) (nat_lit 0) rm i) (fun r =>
    strictB fld(r, nat_lit 60, nat_lit 3) (fun k =>
      strictB fld(r, nat_lit 62, nat_lit 15) (fun p =>
        bAnd(Nat.blt k (nat_lit 3), bAnd(Nat.blt p (nat_lit 9),
          ncAt (Nat.land r (nat_lit 68719476735)) (Y k) (YI k) p)))))

@[expose] noncomputable def thRange (T : Nat → Nat) (rm : Nat) (Y YI : Nat → Nat) (lo cnt : Nat) :
    Bool :=
  allN cnt (fun k => thRec T rm Y YI (Nat.add lo k))

end CFSG.KC.ThI301

end
