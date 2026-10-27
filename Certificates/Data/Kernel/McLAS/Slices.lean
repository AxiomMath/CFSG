module

public import Certificates.Data.Kernel.Spor.MulH

public section

namespace CFSG.KS.McLAS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def recSlK (conj : Bool) (G GI : Nat → Nat) (k cnt : Nat)
    (T PL POS SRT SRI HS HSI : Nat → Nat) (lo len : Nat) : Bool :=
  bAnd(penumSlK (nat_lit 275) (nat_lit 9) (mask (nat_lit 9)) (nat_lit 2475) conj G GI k cnt T PL POS
      SRT SRI lo len,
    slK cnt (hsortPtK (nat_lit 275) (nat_lit 9) (mask (nat_lit 9)) cnt T HS HSI) lo len)

end CFSG.KS.McLAS

end
