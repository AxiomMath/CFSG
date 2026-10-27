module

public import Certificates.Data.Kernel.SporSch.HNXPath

public section

namespace CFSG.KC.LL.HNX

@[expose] def bndW (EN : List Nat) : List Nat → List Nat → Option (List Nat)
  | [], es => some es
  | _ :: _, [] => none
  | l :: ls, e :: es => bif Nat.blt e (lget EN l) then bndW EN ls es else none

@[expose] def bndOk (EN : List Nat) (TW IS : List (List Nat)) : List (List Nat) → List Nat → Bool
  | [], es => es.isEmpty
  | (x :: k :: w) :: ids, es =>
    match bndW EN (lgetL TW x ++ [k]) es with
    | none => false
    | some es₁ =>
      match bndW EN (w ++ lgetL TW (lget (lgetL IS k) x)) es₁ with
      | none => false
      | some es₂ => bndOk EN TW IS ids es₂
  | _ :: _, _ => false

end CFSG.KC.LL.HNX

end
