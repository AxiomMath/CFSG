module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Int.Notation
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.YGroups.ExactData

@[expose] public section

namespace CFSG.YGroups

def y332Arrays : Array (Array ℕ) :=
  ModelNative.withSign (ModelNative.parsePerms ModelNative.y332PermText)

def y332Words : Array (List ℤ) := ModelNative.chainWords ModelNative.y332ChainText

def y332Base : Array ℕ := ModelNative.chainBase ModelNative.y332ChainText

end CFSG.YGroups
