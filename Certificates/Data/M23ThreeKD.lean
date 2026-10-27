module

public import CFSG.Sporadic.Schreier.M23Gens
public import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.Sporadic.Schreier.CountSpec
public import CFSG.Sporadic.Schreier.ClassSum
public import Certificates.Data.CFSGNative.SporadicSchreier.Classes
public meta import CFSG.Sporadic.Schreier.M23Gens
public meta import CFSG.Sporadic.Schreier.Enumeration
public meta import CFSG.Sporadic.Schreier.CountSpec
public meta import CFSG.Sporadic.Schreier.ClassSum
public meta import Certificates.Data.CFSGNative.SporadicSchreier.Classes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264M23

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native

@[expose] def m23S : List (Equiv.Perm (Fin 23)) := [m23PermA, m23PermB]

@[expose] def zW : List Int :=
  [-1, -2, -1, -2, -1, 2, -1, -2, -1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 1, -2, 1, 2, 2, 1, 2,
  1, -2, 1, 2, 2, 1, 2, 1, -2, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -2, -1,
  -2, -2, 1, 2, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2]

@[expose] def m1W : List Int :=
  [-2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, -1, -2, -1, -2, -1, 2, 2, 2, 1, 2, 1,
  -2, 1, 2, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, -1, -2, -1, -2,
  -2, -1, -2, -1, -2, -2, -1, -2]

@[expose] def m2W : List Int :=
  [-2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, -1, 2, -1, -2, -1, 2, -1, 2, -1, -2,
  -2, 1, 2, 1, -2, 1, -2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 2, 1, -2, -1, -2, -1,
  -2, -1, -2, -1, 2, -1, -2, -1, -2, -2, -1, -2, -1, 2]

@[expose] def m3W : List Int :=
  [-2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2,
  -2, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, 2, 1, 2, 1,
  2, 2, 1, 2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2]

end CFSG.LocalAnalysis.GLTheoremA.KD264M23
