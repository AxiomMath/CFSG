module

public import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Monster.B.Mathieu.M22Check
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M22
public meta import CFSG.Monster.B.Mathieu.M22Check
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Th.Native

@[expose] def m22SylowExprs : List (List ℤ) :=
  [[1, 2, 4, 7, -10, 5, 9, 8, 10], [-7, 1, 6, 8, 3, -10, 5, 9, 10], [3, -2, 4, 7, 9, 5, 8],
    [1, -4, 6, -5, -10, 9, 10]]

@[expose] def m22SylowZ : List ℕ :=
  [5, 1, 11, 15, 18, 0, 16, 7, 9, 8, 10, 2, 21, 13, 14, 3, 6, 17, 4, 20, 19, 12]

end CFSG.Sporadic.Schreier
