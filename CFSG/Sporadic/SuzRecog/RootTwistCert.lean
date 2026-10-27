module

public import Certificates.Certificate15112
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Sporadic.SuzRecog.RootTwistCheck

theorem perms_check : permsOK = true :=
  Certificates.certificate15112.1

theorem members_check : membersOK = true :=
  Certificates.certificate15112.2.1

theorem comm_check : commOK = true :=
  Certificates.certificate15112.2.2.1

theorem sq_check : sqOK = true :=
  Certificates.certificate15112.2.2.2.2.1

theorem kGen_check : kGenOK = true :=
  Certificates.certificate15112.2.2.2.2.2.2.1

theorem kEnum_check : kEnumOK = true :=
  Certificates.certificate15112.2.2.2.2.2.2.2.1

theorem kCentre_check : kCentreOK = true :=
  Certificates.certificate15112.2.2.2.2.2.2.2.2.1

theorem class_check : classOK = true :=
  Certificates.certificate15112.2.2.2.2.2.2.2.2.2.1

theorem trans_check : transOK = true :=
  Certificates.certificate15112.2.2.2.2.2.2.2.2.2.2.1

theorem hol_check : holOK = true :=
  Certificates.certificate15112.2.2.2.2.2.2.2.2.2.2.2

end CFSG.Sporadic.SuzRecog.RootTwistCheck
