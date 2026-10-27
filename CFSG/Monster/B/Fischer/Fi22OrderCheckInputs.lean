
module

public import CFSG.Monster.B.Fischer.PinnedChainBase
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Monster.B.Fischer.PinnedChainBase
public meta import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def fi22OrigArrs : Array (Array ℕ) := Array.ofFn fun k : Fin 2 => fi22ChainGen k

@[expose] def fi22BaseArr : Array ℕ := fi22ChainBase.toArray

@[expose] def fi22WordArrs : Array (List ℤ) := Array.ofFn fun j : Fin 19 => fi22Derivation j

@[expose] def powA (n : ℕ) (t : Array ℕ) : ℕ → Array ℕ
  | 0 => idA n
  | e + 1 => compA n t (powA n t e)

end CFSG.Monster.B.Fischer
