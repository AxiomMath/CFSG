module

public import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.M12Pinned
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M12
public meta import CFSG.Sporadic.Schreier.M12Pinned
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

@[expose] def m12SylowExprs : List (List ℤ) :=
  [[-2, 4, 3, 7, 6, -9, 10, 10], [2, -9, 3, -11, 8, -10], [-7, 1, 9, 3, 6, 8, 11, 10],
    [2, -9, 3, 9]]

@[expose] def m12SylowZ : List ℕ :=
  [3, 7, 2, 0, 10, 5, 8, 1, 6, 9, 4, 11]

end CFSG.Sporadic.Schreier
