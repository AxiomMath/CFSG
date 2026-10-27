module

public import CFSG.Monster.Existence.Simple
public import CFSG.Monster.GMS.ExistenceBridge

public section

namespace CFSG.Monster.Existence

theorem gmsLeechCentralizer_xGriess :
    CFSG.Monster.GMS.GMSLeechCentralizer xGriess :=
  CFSG.Monster.GMS.GMSLeechCentralizer.of_isTwoBCentralizer orderOf_xGriess
    (isTwoBCentralizer_MGriess xGriess (IsConj.refl _))

theorem gmsLeechCentralizer_xGmat :
    CFSG.Monster.GMS.GMSLeechCentralizer xGmat :=
  CFSG.Monster.GMS.GMSLeechCentralizer.of_isTwoBCentralizer orderOf_xGmat
    (isTwoBCentralizer_Gmat xGmat (IsConj.refl _))

end CFSG.Monster.Existence
