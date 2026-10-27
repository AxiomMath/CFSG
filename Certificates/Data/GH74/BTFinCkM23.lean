module

public import Certificates.Data.GH74.BTFinCk
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public meta import Certificates.Data.GH74.BTFinCk
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

namespace Certificates.BTFinCk.M23

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

@[expose] def m23FourCk : Bool :=
  centFourOK 23 ((m23CentWords1.map (evalCodes [m23PermA, m23PermB])).map toTable)
    (toTable (m23InvReps.getD 0 1)) 2688 3000 (2 ^ 30 * 3 ^ 30)

end Certificates.BTFinCk.M23
