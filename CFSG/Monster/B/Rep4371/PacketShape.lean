module

public import Certificates.Data.CFSGNative.MonsterB.PacketData
public meta import Certificates.Data.CFSGNative.MonsterB.PacketData
public import Certificates.Certificate3051

public section

namespace CFSG.Monster.B

theorem packetShapeOK_eq_true : Native.packetShapeOK = true :=
  Certificates.certificate3051.1

theorem packetEntryCount_eq : Native.packetEntryCount = 259183 :=
  Certificates.certificate3051.2

end CFSG.Monster.B
