module

public import CFSG.Monster.B.Fischer.PinnedChainData
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Certificates.SchreierChainOrderGenerators
public meta import CFSG.Monster.B.Fischer.PinnedChainData
public meta import CFSG.Monster.B.Co2.PermArr
public import Mathlib.Data.Vector.Basic
public meta import Mathlib.Data.Vector.Basic
public import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.GroupTheory.Perm.Basic

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def fi22StrongArrs : Array (Array ℕ) := Array.ofFn fun j : Fin 19 => fi22ChainStrong j

@[expose] def fi22StrongInvs : Array (Array ℕ) := fi22StrongArrs.map (invCand 3510)

@[expose] def fi22Derivation (j : ℕ) : List ℤ := fi22ChainDerivations.getD (j - 2) []

end CFSG.Monster.B.Fischer
