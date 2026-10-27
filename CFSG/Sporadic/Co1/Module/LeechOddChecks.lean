module

public import CFSG.Sporadic.Co1.Module.OddChecks
public import CFSG.Sporadic.Co1.Module.LeechOddChecksInputs
public import CFSG.Sporadic.Co1.Module.LeechOddLitInputs
public import Certificates.Certificate10071
public meta import CFSG.Sporadic.Co1.Module.OddProg
public meta import CFSG.Sporadic.Co1.Module.OddChecks
public meta import CFSG.Sporadic.Co1.Module.OddNative
public meta import CFSG.Sporadic.Co1.Module.Forms
public meta import CFSG.Sporadic.Co1.Module.Orbits
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Odd
public meta import Certificates.Certificate10073Base
public import Certificates.Certificate10073Base

public section

namespace CFSG.Sporadic.Co1.Module.Odd

theorem noTwoOK_true : noTwoOK = true :=
  Certificates.certificate10071.1

theorem zOneLit_true : zOneLitOK :=
  Certificates.certificate10071.2.1

theorem coverOK_true : coverOK = true :=
  Certificates.certificate10071.2.2.1

theorem zTwoLit_true : zTwoLitOK ∧ orbitYLitOK = true :=
  Certificates.certificate10071.2.2.2.1

theorem tripleOK_true : tripleOK = true :=
  Certificates.certificate10071.2.2.2.2.1

theorem outerLit_true : outerLitOK = true :=
  Certificates.certificate10071.2.2.2.2.2

end CFSG.Sporadic.Co1.Module.Odd
