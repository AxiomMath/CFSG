module

public import CFSG.Monster.Existence.StdOdd.P5
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open CFSG.Monster.Existence.StdOdd.P5 (E5 GL5 M5 rk refl reflGL genA genB Pbar IsExt)

@[expose] def colsData : List (List Nat) :=
  (List.range 30).map fun n => (List.range 5).map fun k =>
    ((refl (Fin.ofNat 6 (n / 5))) (Fin.ofNat 5 k) (Fin.ofNat 5 (n % 5))).val

@[expose] def colVec (i : Fin 6) (j : Fin 5) : E5 := (refl i).mulVec (Pi.single j 1)

@[expose] def pwData : List (List Nat) :=
  (List.range 81).map fun j => (P5.pw (Fin.ofNat 81 j)).map Fin.val

@[expose] def raData : List Nat := (List.range 81).map fun j => (P5.ra (Fin.ofNat 81 j)).val

@[expose] def rbData : List Nat := (List.range 81).map fun j => (P5.rb (Fin.ofNat 81 j)).val

end CFSG.Monster.Existence.StdOdd.Cert
