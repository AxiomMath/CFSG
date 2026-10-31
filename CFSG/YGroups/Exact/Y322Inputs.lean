module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Int.Notation
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.YGroups.ExactData

@[expose] public section

namespace CFSG.YGroups

def y322Arrays : Array (Array ℕ) :=
  ModelNative.parsePerms ModelNative.y322PermText

def y322Words : Array (List ℤ) := ModelNative.chainWords ModelNative.y322ChainText

def y322Base : Array ℕ := ModelNative.chainBase ModelNative.y322ChainText

end CFSG.YGroups
