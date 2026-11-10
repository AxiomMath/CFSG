module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Int.Notation
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.YGroups.ExactData

@[expose] public section

namespace CFSG.YGroups

def y321Arrays : Array (Array ℕ) :=
  ModelNative.parsePerms ModelNative.y321PermText

def y321Words : Array (List ℤ) := ModelNative.chainWords ModelNative.y321ChainText

def y321Base : Array ℕ := ModelNative.chainBase ModelNative.y321ChainText

end CFSG.YGroups
