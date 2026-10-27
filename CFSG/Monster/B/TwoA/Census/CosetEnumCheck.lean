
module

public import CFSG.Monster.B.TwoA.Census.CosetEnumCheckBase

public import CFSG.Monster.B.TwoA.Census.CosetEnumBits
public meta import CFSG.Monster.B.TwoA.Census.CosetEnumBits
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Census.CosetCertData
public meta import CFSG.Monster.B.TwoA.Census.MonoCert
public meta import CFSG.Monster.B.Rep4371.GlueDefs
public meta import Certificates.Data.CFSGNative.MonsterB.CosetEnum
public import CFSG.Monster.B.TwoA.Census.CosetEnumCheckInputs
public import Certificates.Certificate3023

public section

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster.B.Rep4371

theorem countSq_one :
    Native.CosetEnum.countSq (tT 1) (tD 1) (wP 1) = 69632 :=
  Certificates.certificate3023.1

theorem countSq_two :
    Native.CosetEnum.countSq (tT 2) (tD 2) (wP 2) = 8192 :=
  Certificates.certificate3023.2.1

theorem countSq_six :
    Native.CosetEnum.countSq (tT 6) (tD 6) (wP 6) = 0 :=
  Certificates.certificate3023.2.2.1

theorem classCheck_eq_true : classCheck = true :=
  Certificates.certificate3023.2.2.2.1

theorem class17Check_eq_true : class17Check = true :=
  Certificates.certificate3023.2.2.2.2.1

theorem class2Check_eq_true : class2Check = true :=
  Certificates.certificate3023.2.2.2.2.2

end CFSG.Monster.B.TwoA.Census
