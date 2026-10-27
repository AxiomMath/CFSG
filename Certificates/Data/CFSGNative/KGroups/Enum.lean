module

public import Certificates.Data.CFSGNative.KGroups.Perm

public section

namespace CFSG.KGroups.Native

open CFSG.Monster.B.Co2.Native

@[expose] def productsA (n : Nat) : List (List (Array Nat)) → List (Array Nat)
  | [] => [idA n]
  | T :: Ts =>
    let P := productsA n Ts
    T.flatMap fun t => P.map (compA n t)

@[expose] def powInA (n : Nat) (LA LP : List (Array Nat)) (k : Nat) : Bool :=
  LA.all fun g => !eqA n (powA n g k) (idA n) || LP.any fun q => eqA n g q

end CFSG.KGroups.Native
