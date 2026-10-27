module

public import Certificates.Certificate15110

public section

namespace CFSG.Sporadic.SuzRecog.B0Gluing

theorem b0Idx_check : idxCheck = true :=
  Certificates.certificate15110.1

theorem b0Theta_check : thetaCheck = true :=
  Certificates.certificate15110.2.1

theorem b0Aut_check : autCheck = true :=
  Certificates.certificate15110.2.2.1

theorem b0Plane_check : planeCheck = true :=
  Certificates.certificate15110.2.2.2.1

theorem b0CentR_check : centRCheck = true :=
  Certificates.certificate15110.2.2.2.2.1

theorem b0TauZ_check : tauZCheck = true :=
  Certificates.certificate15110.2.2.2.2.2.1

theorem b0RhoA_check : rhoACheck = true :=
  Certificates.certificate15110.2.2.2.2.2.2

end CFSG.Sporadic.SuzRecog.B0Gluing
