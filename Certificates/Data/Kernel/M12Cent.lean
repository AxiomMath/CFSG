module

public import CFSG.GH74.M12.HypCoreInputs

public section

namespace CFSG.KC.M12Cent

open CFSG.GH74.M12.Hyp

@[expose] def tAk : List Nat := [3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5]

@[expose] def tBk : List Nat := [7, 2, 3, 1, 11, 9, 5, 8, 0, 6, 4, 10]

@[expose] def tBi : List Nat := [8, 3, 1, 2, 10, 6, 9, 0, 7, 5, 11, 4]

@[expose] def letN : Nat → List Nat
  | 0 => tAk
  | 1 => tAk
  | 2 => tBk
  | _ => tBi

@[expose] def letInv : Nat → List Nat
  | 0 => tAk
  | 1 => tAk
  | 2 => tBi
  | _ => tBk

@[expose] def wordN : List Nat → List Nat
  | [] => tid
  | l :: w => tmul (letN l) (wordN w)

@[expose] def conjN : List Nat → List Nat → List Nat
  | [], t => t
  | l :: w, t => tmul (tmul (letN l) (conjN w t)) (letInv l)

@[expose] def keyT (t : List Nat) : Nat := t.foldr (fun a k => a + 16 * k) 0

@[expose] def incr : List Nat → Bool
  | a :: b :: r => Nat.blt a b && incr (b :: r)
  | _ => true

@[expose] def centCheck (t : List Nat) (S W C R : List (List Nat)) : Bool :=
  W.length == 1760 && C.length == 54 && incr (W.map fun w => keyT (conjN w t)) &&
    C.all (fun w => tmul (wordN w) t == tmul t (wordN w)) &&
    incr (C.map fun w => keyT (wordN w)) &&
    S.all fun s => s == tid || R.any fun w => conjN w t == s

end CFSG.KC.M12Cent

end
