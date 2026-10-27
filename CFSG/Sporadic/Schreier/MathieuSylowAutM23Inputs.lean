module

public import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.M23Pinned
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M23
public meta import CFSG.Sporadic.Schreier.M23Pinned
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import CFSG.Sporadic.M23.M23Group
public meta import CFSG.Sporadic.M23.M23Group
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Th.Native

@[expose] def m23SylowExprs : List (List ℤ) :=
  [[2, 1, 8, 3, -9, 8, -11, 15], [12, -2, 1, 7, 3, 12, 5, -9, 8, 15, 12],
    [1, -2, 14, 3, 9, 5, 14, 9, -11, 15, 14, 12], [5, -2, 11, 3, 7, 12, 5, 11, 8, 11, 13]]

@[expose] def m23SylowZ : List ℕ :=
  [7, 6, 9, 8, 4, 5, 1, 0, 3, 2, 10, 11, 19, 18, 21, 20, 16, 17, 13, 12, 15, 14, 22]

end CFSG.Sporadic.Schreier
