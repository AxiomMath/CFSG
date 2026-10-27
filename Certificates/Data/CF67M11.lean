module

public import Certificates.Data.CF67Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11Data
public meta import Certificates.Data.CF67Check
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM11Data
public meta import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace Certificates.CF67.M11

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

@[expose] def wa : List ℤ :=
  [2, 2, 2, -1, -2, -2, -1, -2, -1, -2, -2]

@[expose] def wb : List ℤ :=
  [-1, -2, -1, 2, 2, 1, 2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1, -2, -1, -2, -2, -1, -2, -1, -2, -2,
   -1, -2, -2, -1]

@[expose] def m11CF67OK : Bool :=
  cf67OK 11 m11Certificate [m11gA, m11gB] 3 wa wb

end Certificates.CF67.M11
