module

public import Certificates.Data.CFSGNative.MonsterB.PacketCheck
public meta import Certificates.Data.CFSGNative.MonsterB.PacketCheck
public import Certificates.Certificate3050

public section

namespace CFSG.Monster.B.Rep4371

theorem genCheck_pauli :
    ((List.range 23).all fun i => Native.genCheck i) = true :=
  Certificates.certificate3050.1

theorem genCheck_perm :
    ((List.range 12).all fun i => Native.genCheck (23 + i)) = true :=
  Certificates.certificate3050.2.1

theorem genCheck_sign :
    ((List.range 11).all fun i => Native.genCheck (35 + i)) = true :=
  Certificates.certificate3050.2.2.1

theorem genCheck_xi : Native.genCheck 46 = true :=
  Certificates.certificate3050.2.2.2.1

theorem tauCheck_eq_true : Native.tauCheck = true :=
  Certificates.certificate3050.2.2.2.2.1

theorem labelsCheck_eq_true :
    Native.labelsCheck = true ∧ Native.spinIndexCheck = true :=
  Certificates.certificate3050.2.2.2.2.2.1

theorem octCheck_eq_true :
    Native.octDataOK = true ∧ Native.octSignOK = true :=
  Certificates.certificate3050.2.2.2.2.2.2

end CFSG.Monster.B.Rep4371
