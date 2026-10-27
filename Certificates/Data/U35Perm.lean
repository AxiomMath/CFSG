module

public import CFSG.Quasithin.Vol2.KGFactU35Inputs

public section

namespace U35Perm

open HNUnitaryBridge
open CFSG.Quasithin.H13.KGU35 (cConj)

@[expose] def rCode : Array Nat := #[5, 5, 0, 20, 5, 0, 0, 0, 4]

@[expose] def sCode : Array Nat := #[0, 1, 0, 1, 0, 0, 0, 0, 4]

@[expose] def tList : List (Array Nat) :=
  (List.range 8).flatMap fun i =>
    [CFSG.Quasithin.H13.KGU35.mPow rCode i,
      CFSG.Quasithin.H13.KGU35.mMul (CFSG.Quasithin.H13.KGU35.mPow rCode i) sCode]

end U35Perm
