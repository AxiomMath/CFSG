module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Int.Notation
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.YGroups.Model233FData

@[expose] public section

namespace CFSG.YGroups

@[expose] def y233FArrays : Array (Array ℕ) := ModelNative.parsePerms ModelNative.y233FPermText

@[expose] def y233FWords : Array (List ℤ) := ModelNative.chainWords ModelNative.y233FChainText

@[expose] def y233Base : List (Fin 3510) := [0, 1, 2, 3, 5, 9, 12]

@[expose] def y233FStrong : Array (Array ℕ) :=
  (ModelNative.strongOf 3510 y233FArrays y233FWords).1

@[expose] def y233FRawWords : Array (List ℤ) := Array.replicate 9 [] ++ y233FWords

@[expose] def y233CArrays : Array (Array ℕ) :=
  #[y233FArrays[0]!, y233FArrays[1]!, y233FArrays[3]!, y233FArrays[4]!, y233FArrays[5]!,
    y233FArrays[6]!, y233FArrays[7]!, y233FArrays[8]!]

@[expose] def y233CWords : Array (List ℤ) := ModelNative.chainWords ModelNative.y233CChainText

@[expose] def y233CStrong : Array (Array ℕ) :=
  (ModelNative.strongOf 3510 y233CArrays y233CWords).1

@[expose] def y233CRawWords : Array (List ℤ) := Array.replicate 8 [] ++ y233CWords

end CFSG.YGroups
