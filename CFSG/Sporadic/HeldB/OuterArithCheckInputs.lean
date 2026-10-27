module

public import CFSG.Sporadic.HeldB.AutData
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.HeldB.AutData
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Sporadic.HeldB

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def hePowA (t : Array ℕ) : ℕ → Array ℕ
  | 0 => idA 8330
  | e + 1 => compA 8330 t (hePowA t e)

@[expose] def heW2Arr : Array ℕ := hePowA (compA 8330 (heGen 0) (hePowA (heGen 1) 2)) 2

end CFSG.Sporadic.HeldB
