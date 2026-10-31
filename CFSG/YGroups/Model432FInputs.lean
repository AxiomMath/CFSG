module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Int.Notation
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.YGroups.Model432FData

@[expose] public section

namespace CFSG.YGroups


def y432FArrays : Array (Array ℕ) := ModelNative.parsePerms ModelNative.y432FPermText

def y432FWords : Array (List ℤ) := ModelNative.chainWords ModelNative.y432FChainText

def y432FBase : Array ℕ := ModelNative.chainBase ModelNative.y432FChainText

def y432CBase : List (Fin 31671) := [0, 52, 166, 722, 1, 3, 10, 5, 8]

def y432CArrays : Array (Array ℕ) :=
  #[y432FArrays[0]!, y432FArrays[1]!, y432FArrays[2]!, y432FArrays[3]!, y432FArrays[4]!,
    y432FArrays[5]!, y432FArrays[6]!, y432FArrays[7]!, y432FArrays[8]!]

def y432CWords : Array (List ℤ) := ModelNative.chainWords ModelNative.y432CChainText

def y432CStrong : Array (Array ℕ) :=
  (ModelNative.strongOf 31671 y432CArrays y432CWords).1

def y432CRawWords : Array (List ℤ) := Array.replicate 9 [] ++ y432CWords

def F432Word : List ℕ := (List.replicate 9 [0, 5, 6, 7, 8, 9, 1]).flatten

def F432AltWord : List ℕ := (List.replicate 9 [0, 5, 6, 7, 1, 2, 8]).flatten

end CFSG.YGroups
