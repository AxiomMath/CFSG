module

public import Certificates.Data.CF67Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public meta import Certificates.Data.CF67Check
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public import CFSG.Sporadic.M23.M23Group
public meta import CFSG.Sporadic.M23.M23Group
public meta import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.Schreier.M23Base
public meta import CFSG.Sporadic.Schreier.M23Base
public import CFSG.Sporadic.Schreier.M23CheckBase
public meta import CFSG.Sporadic.Schreier.M23CheckBase
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.Outer
public meta import CFSG.Sporadic.Schreier.Outer

public section

namespace Certificates.CF67.M23

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

@[expose] def wa : List ℤ :=
  [2, 1, -2, -1, -1, -2, -2, -1, -2, -2, -1, 2, -1, -2, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2,
   -1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 2, 1, 2, 1, -2, -1, -2, -1, -2, -2, -1, 2, -1,
   -2, -1, 2, -1, 2, -1, -2, -2, 1, 2, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2]

@[expose] def wb : List ℤ :=
  [1, 2, 2, 1, -2, 1, 2, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, -1, 2, -1, -2,
   -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -2, -1,
   -2, -1, -2, -2, -1, -2, -2, -1, -2, -2, -1, 2]

@[expose] def m23CF67OK : Bool :=
  cf67OK 23 m23Certificate [m23PermA, m23PermB] 3 wa wb

end Certificates.CF67.M23
