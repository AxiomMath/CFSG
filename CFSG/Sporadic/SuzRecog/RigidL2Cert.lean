module

public import Certificates.Certificate15100

public section

namespace CFSG.Sporadic.SuzRecog.RigidL2

theorem rigLift_check : rigLiftOK = true :=
  Certificates.certificate15100.1

theorem rigUComplete_check : rigUCompleteOK = true :=
  Certificates.certificate15100.2.1

theorem rigGen_check : rigGenOK = true :=
  Certificates.certificate15100.2.2.1

theorem rigComm_check : rigCommOK = true :=
  Certificates.certificate15100.2.2.2.1

theorem rigDecomp_check : rigDecompOK = true :=
  Certificates.certificate15100.2.2.2.2.1

theorem rigCenter_check : rigCenterOK = true :=
  Certificates.certificate15100.2.2.2.2.2.1

theorem rigStab_check : rigStabOK = true :=
  Certificates.certificate15100.2.2.2.2.2.2.1

theorem rigX1_check : rigX1OK = true :=
  Certificates.certificate15100.2.2.2.2.2.2.2.1

theorem rigX2_check : rigX2OK = true :=
  Certificates.certificate15100.2.2.2.2.2.2.2.2.1

theorem rigBfs_check : rigBfsOK = true :=
  Certificates.certificate15100.2.2.2.2.2.2.2.2.2.1

theorem rigIrred_check : rigIrredOK = true :=
  Certificates.certificate15100.2.2.2.2.2.2.2.2.2.2

end CFSG.Sporadic.SuzRecog.RigidL2
