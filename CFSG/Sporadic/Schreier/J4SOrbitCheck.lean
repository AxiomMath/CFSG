
module

public import CFSG.Sporadic.Schreier.J4SOrbitCheckBase

public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import Certificates.Certificate2177

public section

namespace CFSG.Sporadic.J4Schreier

theorem orb1_ok : bfsOK xyGens 1 1771 orb1 = true :=
  Certificates.certificate2177.1

theorem orb14_ok : bfsOK xyGens 14 276 orb14 = true :=
  Certificates.certificate2177.2.1

theorem coverCheck_eq : coverCheck = true :=
  Certificates.certificate2177.2.2.1

theorem orb1_closed : closedOK xyInvGens orb1.1 1771 = true :=
  Certificates.certificate2177.2.2.2.1

theorem orb14_closed : closedOK xyInvGens orb14.1 276 = true :=
  Certificates.certificate2177.2.2.2.2.1

theorem fixCheck_eq : fixCheck = true :=
  Certificates.certificate2177.2.2.2.2.2.1

theorem orbB_ok : bfsOK gens1 2 1440 orbB = true :=
  Certificates.certificate2177.2.2.2.2.2.2.1

theorem orbC_ok : bfsOK gens2 4 96 orbC = true :=
  Certificates.certificate2177.2.2.2.2.2.2.2

end CFSG.Sporadic.J4Schreier
