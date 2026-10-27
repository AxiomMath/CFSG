module

public import Certificates.Data.CF67Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterData
public meta import Certificates.Data.CF67Check
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterData
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreOuter

public section

namespace Certificates.CF67.M22

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

@[expose] def wa : List ℤ :=
  [-2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, 2, 1, 2, 1, 2, 2, 1, -2, 1, -2,
   1, 2, 1, 2, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1]

@[expose] def wb : List ℤ :=
  [-1, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, 2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1, 2, 2, 1, 2, 1,
   2, 1, 1, 2, 1, 2, 2, 1, -2, 1, 2, 1, 2, 1, 2, 2, -1, -2, -1, -2]

@[expose] def m22CF67OK : Bool :=
  cf67OK 22 m22Certificate [m22gA, m22gB] 3 wa wb

end Certificates.CF67.M22
