module

public import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Monster.B.Mathieu.M24Check
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M24
public meta import CFSG.Monster.B.Mathieu.M24Check
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

@[expose] def m24SylowExprs : List (List ℤ) :=
  [[4, -2, 4, -3, 4, 5, 7, 6, -13], [4, -2, -10, 3, 10, 5, -6, -12, -13, -9, -14],
    [4, -2, -3, 8, 5, 13, 6, 10, 7, 9, 13, 9, 14], [4, -2, 8, 3, 4, 5, 7, 6, 10, 8, 14],
    [3, 1, -14, -3, -11, 8, 9, 6, -10, 8, -9, -13, -14],
    [1, -5, 3, -5, 4, 14, -6, 13, 7, 14, 9, 14]]

@[expose] def m24SylowZ : List ℕ :=
  [0, 15, 10, 3, 21, 5, 13, 23, 8, 9, 2, 11, 22, 6, 19, 1, 17, 16, 18, 14, 20, 4, 12, 7]

end CFSG.Sporadic.Schreier
