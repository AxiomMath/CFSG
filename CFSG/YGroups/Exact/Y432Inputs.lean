module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Int.Notation
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.YGroups.ExactData

@[expose] public section

namespace CFSG.YGroups

@[expose] def y432Arrays : Array (Array ℕ) :=
  ModelNative.withSign (ModelNative.parsePerms ModelNative.y432PermText)

@[expose] def y432Words : Array (List ℤ) := ModelNative.chainWords ModelNative.y432ChainText

@[expose] def y432Base : Array ℕ := ModelNative.chainBase ModelNative.y432ChainText

end CFSG.YGroups
